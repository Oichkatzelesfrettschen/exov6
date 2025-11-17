# Phase 5.6: Filesystem Lock Strategy

**Date:** 2025-11-17
**Status:** Design Complete (Implementation in Phase 7)

---

## Executive Summary

The ExoV6 filesystem uses multiple locks at different granularities:
- **Cache locks** (icache, bcache): Short-duration spinlocks for cache lookup
- **Per-object sleeplocks** (inode, buffer): Long-duration locks for I/O operations
- **Subsystem locks** (fs_log, idelock): Filesystem log and device driver locks

This document defines a comprehensive lock hierarchy integrating these locks with the DAG lock ordering system for deadlock prevention.

---

## Current Filesystem Lock Inventory

### 1. Inode Cache Lock (`icache.lock`)

**File:** `kernel/fs/fs.c:221-223`

```c
struct {
  struct spinlock lock;  // ← To be migrated
  struct inode inode[NINODE];
} icache;
```

**Purpose:** Protects inode cache allocation and reference counting

**Critical sections:**
- Inode lookup (`iget`)
- Inode allocation
- Reference count updates

**Duration:** < 100 cycles (short)

**Recommendation:** **qspinlock** at `LOCK_LEVEL_FILESYSTEM` (40)

---

### 2. Buffer Cache Lock (`bcache.lock`)

**File:** `kernel/fs/bio.c:30-38`

```c
struct {
  struct spinlock lock;   // ← To be migrated
  struct buf buf[NBUF];
  struct spinlock rlock;  // RCU lock ← To be migrated
  struct buf head;
} bcache;
```

**Purpose:** Protects buffer cache LRU list and buffer allocation

**Critical sections:**
- Buffer lookup (`bget`)
- Buffer allocation
- LRU list manipulation

**Duration:** < 200 cycles (short)

**Recommendation:** **qspinlock** at `LOCK_LEVEL_FILESYSTEM` (40)

**RCU lock:** Also migrate to **qspinlock** at `LOCK_LEVEL_FILESYSTEM` (40)

---

### 3. Per-Inode Sleeplocks

**File:** `kernel/fs/fs.c:230`

```c
// In iinit()
initsleeplock(&icache.inode[i].lock, "inode");
```

**Purpose:** Protects individual inode contents during I/O operations

**Critical sections:**
- Reading/writing inode metadata
- Block allocation/deallocation
- Directory operations

**Duration:** Variable (can span disk I/O, ~10ms)

**Recommendation:** **sleeplock** at `LOCK_LEVEL_FILESYSTEM + 1` (41)

**Rationale:** Must be higher than icache.lock to allow:
```c
acquire(&icache.lock);        // Level 40
acquiresleep(&inode->lock);   // Level 41 - OK!
```

---

### 4. Filesystem Log Lock (`fs_log.lock`)

**File:** `kernel/fs/log.c:41`

```c
struct log {
  struct spinlock lock;  // ← To be migrated
  // ... log metadata ...
};
```

**Purpose:** Protects filesystem log metadata

**Critical sections:**
- Log commit
- Transaction management

**Duration:** < 500 cycles (medium)

**Recommendation:** **adaptive_mutex** at `LOCK_LEVEL_FILESYSTEM` (40)

**Rationale:** Log operations may contend during heavy write workloads; adaptive_mutex provides better performance than spinning

---

### 5. IDE Disk Lock (`idelock`)

**File:** `kernel/fs/ide.c:31`

```c
static struct spinlock idelock;  // ← To be migrated
```

**Purpose:** Protects IDE disk controller state

**Critical sections:**
- Disk I/O initiation
- Interrupt handling

**Duration:** < 50 cycles (very short)

**Recommendation:** **qspinlock** at `LOCK_LEVEL_DEVICE` (50)

**Rationale:** Device-level lock, should be at DEVICE tier

---

## Proposed DAG Lock Hierarchy

```
ExoV6 Filesystem Lock Hierarchy

LOCK_LEVEL_SCHEDULER (10)
    └─ Scheduler locks (ptable.lock)

LOCK_LEVEL_MEMORY (20)
    └─ Memory allocator (kmem.lock[])

LOCK_LEVEL_PROCESS (30)
    └─ Process table (already at scheduler level, see note below)

LOCK_LEVEL_FILESYSTEM (40) ← FS cache tier
    ├─ icache.lock (qspinlock)
    ├─ bcache.lock (qspinlock)
    ├─ bcache.rlock (qspinlock)
    └─ fs_log.lock (adaptive_mutex)

LOCK_LEVEL_FILESYSTEM + 1 (41) ← Per-inode tier
    └─ inode->lock (sleeplock)

LOCK_LEVEL_FILESYSTEM + 2 (42) ← Per-buffer tier
    └─ buf->lock (sleeplock, if added)

LOCK_LEVEL_DEVICE (50)
    ├─ idelock (qspinlock)
    ├─ cons.lock (qspinlock)
    └─ uart.lock (qspinlock)

LOCK_LEVEL_NETWORK (60)
    └─ Network stack locks (future)

LOCK_LEVEL_CAPABILITY (70)
    └─ Capability system locks (future)

LOCK_LEVEL_USER (80)
    └─ User-facing locks
```

**Note:** In ExoV6, the process table lock (`ptable.lock`) is actually used by the scheduler, so it's effectively at the scheduler tier (LOCK_LEVEL_PROCESS = 30), which we've already set.

---

## Lock Ordering Rules

### Rule 1: Cache Before Object

Always acquire cache locks before per-object locks:

```c
// CORRECT: Cache lock → Object lock
qspin_lock(&icache.lock);           // Level 40
ip = find_inode(...);
qspin_unlock(&icache.lock);
acquiresleep(&ip->lock);            // Level 41 - OK!
```

```c
// WRONG: Object lock → Cache lock (would violate DAG)
acquiresleep(&ip->lock);            // Level 41
qspin_lock(&icache.lock);           // Level 40 - VIOLATION!
```

### Rule 2: Filesystem Before Device

Filesystem operations may trigger disk I/O, so filesystem locks must be lower than device locks:

```c
// CORRECT: Filesystem → Device
qspin_lock(&bcache.lock);           // Level 40
// ... lookup buffer ...
qspin_unlock(&bcache.lock);
qspin_lock(&idelock);               // Level 50 - OK!
ide_start_rw(buf);
qspin_unlock(&idelock);
```

### Rule 3: No Memory Allocation Inside Filesystem Locks

Since `LOCK_LEVEL_MEMORY` (20) < `LOCK_LEVEL_FILESYSTEM` (40), calling `kalloc()` while holding a filesystem lock would violate DAG:

```c
// WRONG: FS lock → Memory allocation
qspin_lock(&icache.lock);           // Level 40
char *p = kalloc();                 // Tries level 20 - VIOLATION!
```

**Solution:** Allocate memory **before** acquiring filesystem locks:

```c
// CORRECT: Allocate first, then lock
char *p = kalloc();                 // Level 20
qspin_lock(&icache.lock);           // Level 40 - OK!
// ... use p ...
qspin_unlock(&icache.lock);
```

### Rule 4: Multiple Inodes in Consistent Order

When locking multiple inodes, always lock in a consistent order (e.g., by inode number):

```c
// Rename: moves file from dir1 to dir2
void rename(struct inode *dir1, struct inode *dir2) {
    struct inode *first, *second;

    // Lock in inode number order to prevent deadlock
    if (dir1->inum < dir2->inum) {
        first = dir1;
        second = dir2;
    } else {
        first = dir2;
        second = dir1;
    }

    acquiresleep(&first->lock);   // Level 41
    acquiresleep(&second->lock);  // Level 41

    // Both at same level, but consistent order prevents deadlock

    releasesleep(&second->lock);
    releasesleep(&first->lock);
}
```

**Note:** DAG allows same-level locks if acquired in consistent order. The inode number ordering ensures this.

---

## Migration Plan

### Phase 7.4: Filesystem Cache Locks (P1 Priority)

**Files to modify:**
- `kernel/fs/fs.c` (icache)
- `kernel/fs/bio.c` (bcache)
- `kernel/fs/log.c` (fs_log)

**Steps:**

1. **Update icache.lock:**
   ```c
   // In iinit()
   qspin_init(&icache.lock, "icache", LOCK_LEVEL_FILESYSTEM);

   // Replace all acquire/release calls
   acquire(&icache.lock) → qspin_lock(&icache.lock)
   release(&icache.lock) → qspin_unlock(&icache.lock)
   ```

2. **Update bcache.lock:**
   ```c
   // In binit()
   qspin_init(&bcache.lock, "bcache", LOCK_LEVEL_FILESYSTEM);
   qspin_init(&bcache.rlock, "bcache_rcu", LOCK_LEVEL_FILESYSTEM);

   // Replace all acquire/release calls
   ```

3. **Update fs_log.lock:**
   ```c
   // In initlog()
   adaptive_mutex_init(&fs_log.lock, "fs_log", LOCK_LEVEL_FILESYSTEM);

   // Replace acquire/release with adaptive_mutex_lock/unlock
   ```

4. **Update per-inode sleeplocks:**
   ```c
   // In iinit()
   initsleeplock(&icache.inode[i].lock, "inode", LOCK_LEVEL_FILESYSTEM + 1);

   // acquiresleep/releasesleep remain unchanged (DAG hooks added in Phase 6)
   ```

**Estimated effort:** 6-8 hours

**Risk:** HIGH (filesystem is critical)

### Phase 7.5: Device Locks (P2 Priority)

**Files to modify:**
- `kernel/fs/ide.c` (idelock)

**Steps:**

1. **Update idelock:**
   ```c
   // In ideinit()
   qspin_init(&idelock, "ide", LOCK_LEVEL_DEVICE);
   ```

**Estimated effort:** 1 hour

**Risk:** MEDIUM

---

## Testing Strategy

### Unit Tests

**Test 1: Cache lock ordering**
```c
void test_fs_cache_ordering(void) {
    // Acquire in correct order
    qspin_lock(&icache.lock);      // Level 40
    qspin_lock(&bcache.lock);      // Level 40 (same level, separate data)

    qspin_unlock(&bcache.lock);
    qspin_unlock(&icache.lock);

    // Should succeed: No violations
}
```

**Test 2: Inode sleeplock ordering**
```c
void test_inode_lock_ordering(void) {
    struct inode *ip;

    qspin_lock(&icache.lock);      // Level 40
    ip = find_inode(1);
    qspin_unlock(&icache.lock);

    acquiresleep(&ip->lock);       // Level 41 - OK
    releasesleep(&ip->lock);
}
```

**Test 3: Filesystem → Device**
```c
void test_fs_device_ordering(void) {
    qspin_lock(&bcache.lock);      // Level 40
    qspin_unlock(&bcache.lock);

    qspin_lock(&idelock);          // Level 50 - OK
    qspin_unlock(&idelock);
}
```

**Test 4: Memory allocation violation**
```c
void test_fs_memory_violation(void) {
    qspin_lock(&icache.lock);      // Level 40

    // This should trigger DAG violation
    char *p = kalloc();            // Tries level 20 - VIOLATION!

    // DAG will panic or warn
}
```

### Integration Tests

**Test 5: File I/O stress test**
```bash
# Run from userspace
for i in {1..1000}; do
    echo "test $i" > /file$i &
done
wait

# Check for DAG violations in kernel log
dmesg | grep "DAG VIOLATION"
```

**Test 6: Rename stress test**
```bash
# Test multi-inode locking
for i in {1..100}; do
    mv /file$i /newfile$i &
done
wait
```

---

## Performance Considerations

### Expected Impact

| Lock | Old Type | New Type | Expected Latency | Change |
|------|----------|----------|------------------|--------|
| **icache.lock** | spinlock | qspinlock | ~23 cycles | 0% (NUMA benefit) |
| **bcache.lock** | spinlock | qspinlock | ~23 cycles | 0% |
| **fs_log.lock** | spinlock | adaptive_mutex | ~38 cycles (uncontended) | +15 cycles |
| **idelock** | spinlock | qspinlock | ~23 cycles | 0% |

**DAG Overhead:**
- Validation: ~28 cycles per acquisition
- Tracking: ~35 cycles per acquisition
- **Total:** ~63 cycles additional overhead

**Net Impact on File I/O:**
- Metadata operations: +63 cycles (~1% slowdown)
- Bulk I/O: Negligible (dominated by disk latency ~10ms)

**NUMA Benefit:**
- Multi-socket systems: 20-30% improvement for cache-heavy workloads
- Single-socket: No regression

---

## Common Patterns

### Pattern 1: Read File Metadata

```c
struct inode *ip;

// 1. Look up inode in cache
qspin_lock(&icache.lock);           // Level 40
ip = iget(dev, inum);
ip->ref++;
qspin_unlock(&icache.lock);

// 2. Lock inode for reading
acquiresleep(&ip->lock);            // Level 41
// ... read inode metadata ...
releasesleep(&ip->lock);

// 3. Release reference
iput(ip);
```

### Pattern 2: Allocate Disk Block

```c
// Pre-allocate memory BEFORE filesystem locks
char *buf = kalloc();               // Level 20

// Now safe to use filesystem locks
qspin_lock(&bcache.lock);           // Level 40
struct buf *bp = bget(dev, blockno);
qspin_unlock(&bcache.lock);

// Use buffer...

brelse(bp);
```

### Pattern 3: Filesystem Transaction

```c
begin_op();                         // Acquires fs_log.lock (level 40)

struct inode *ip = ialloc(...);     // Acquires icache.lock (level 40)
acquiresleep(&ip->lock);            // Level 41

// ... modify inode ...

releasesleep(&ip->lock);
iupdate(ip);

end_op();                           // Releases fs_log.lock
```

---

## Debugging DAG Violations

### Common Violation: Memory Allocation Inside FS Lock

**Violation Report:**
```
=== DAG VIOLATION DETECTED ===
Attempted acquisition:
  Lock:   kmem_node0 (0xffff880012340)
  Level:  20
  Type:   qspinlock
  Source: kalloc.c:107

Currently held locks (1):
  [0] icache (level 40, qspinlock) at fs.c:292

Violation: Level 20 <= 40 (must be strictly increasing)
```

**Fix:**
```c
// BEFORE (wrong)
qspin_lock(&icache.lock);
char *p = kalloc();  // VIOLATION!
qspin_unlock(&icache.lock);

// AFTER (correct)
char *p = kalloc();  // Allocate first
qspin_lock(&icache.lock);
// ... use p ...
qspin_unlock(&icache.lock);
```

### Common Violation: Reverse Inode Locking

**Problem:** Two threads lock the same pair of inodes in opposite order

**Solution:** Always lock in inode number order (see Rule 4)

---

## Migration Checklist

- [ ] Identify all filesystem locks (✅ Done in this document)
- [ ] Design lock hierarchy (✅ Done)
- [ ] Update icache.lock to qspinlock
- [ ] Update bcache.lock to qspinlock
- [ ] Update bcache.rlock to qspinlock
- [ ] Update fs_log.lock to adaptive_mutex
- [ ] Update idelock to qspinlock
- [ ] Update per-inode sleeplocks with DAG levels (Phase 6)
- [ ] Test with file I/O stress
- [ ] Test with rename stress
- [ ] Verify no DAG violations
- [ ] Performance benchmarks

---

## Conclusion

The filesystem lock hierarchy integrates cleanly with the DAG lock ordering system:

✅ **Three-tier architecture:**
- Tier 1: Cache locks (qspinlock, level 40)
- Tier 2: Per-object locks (sleeplock, level 41-42)
- Tier 3: Device locks (qspinlock, level 50)

✅ **Clear ordering rules:**
- Cache before object
- Filesystem before device
- Memory allocation before filesystem

✅ **Expected benefits:**
- Automatic deadlock prevention
- NUMA performance improvements
- Clear lock hierarchy for developers

**Implementation:** Phase 7.4 (filesystem) + Phase 7.5 (device)

**Risk mitigation:** Extensive testing before production use

---

**Next:** Phase 7 Lock Migration (implementation)

**Signed:** Phase 5.6 Filesystem Lock Strategy
**Date:** 2025-11-17
