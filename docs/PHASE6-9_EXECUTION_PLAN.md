# Phases 6-9 Execution Plan

**Date:** 2025-11-17
**Status:** Ready to Execute
**Scope:** Sleeplock modernization → Lock migration → Validation → Documentation

---

## Overview

Phases 6-9 complete the lock subsystem modernization journey:
- **Phase 6**: Add DAG integration to sleeplocks (foundation)
- **Phase 7**: Migrate remaining kernel locks (implementation)
- **Phase 8**: Real-world validation and testing (verification)
- **Phase 9**: Developer documentation (knowledge transfer)

**Estimated Total Effort:** 8-12 hours
**Risk Level:** Medium to High (touches critical paths)

---

## Phase 6: Sleeplock Modernization

**Goal:** Integrate existing sleeplocks with DAG lock ordering

**Status:** Sleeplocks already exist, just need DAG hooks

**Estimated Effort:** 2-3 hours
**Risk:** Medium (sleeplocks used for I/O operations)

### 6.1: Sleeplock Structure Update

**File:** `include/sleeplock.h`

**Current:**
```c
struct sleeplock {
  uint locked;
  struct spinlock lk;  // Internal lock
  char *name;
  int pid;
};
```

**Updated:**
```c
struct sleeplock {
  uint locked;
  struct qspinlock lk;     // Modernize internal lock!
  char *name;
  uint32_t dag_level;      // Add DAG level
  int pid;
};
```

### 6.2: Sleeplock DAG Integration

**File:** `kernel/sync/sleeplock.c`

**Changes needed:**

1. **Update initialization:**
```c
void initsleeplock(struct sleeplock *lk, char *name, uint32_t dag_level) {
  // Internal lock at dag_level - 1 (must be lower than sleeplock itself)
  qspin_init(&lk->lk, "sleeplock_internal", dag_level > 0 ? dag_level - 1 : 0);
  lk->name = name;
  lk->dag_level = dag_level;
  lk->locked = 0;
  lk->pid = 0;
}
```

2. **Add DAG validation in acquiresleep:**
```c
void acquiresleep(struct sleeplock *lk) {
#ifdef USE_DAG_CHECKING
  // Validate before acquiring
  if (!dag_validate_acquisition(lk, lk->name, lk->dag_level,
                                LOCK_TYPE_SLEEP, __FILE__, __LINE__)) {
    panic("acquiresleep: DAG violation");
  }
#endif

  qspin_lock(&lk->lk);  // Acquire internal lock

  while (lk->locked) {
    sleep(lk, &lk->lk);  // Sleep, releasing internal lock
  }

  lk->locked = 1;
  lk->pid = myproc()->pid;

#ifdef USE_DAG_CHECKING
  // Track acquisition
  dag_lock_acquired(lk, lk->name, lk->dag_level,
                   LOCK_TYPE_SLEEP, __FILE__, __LINE__);
#endif

  qspin_unlock(&lk->lk);  // Release internal lock
}
```

3. **Add DAG tracking in releasesleep:**
```c
void releasesleep(struct sleeplock *lk) {
  qspin_lock(&lk->lk);

#ifdef USE_DAG_CHECKING
  dag_lock_released(lk);  // Track release
#endif

  lk->locked = 0;
  lk->pid = 0;
  wakeup(lk);

  qspin_unlock(&lk->lk);
}
```

### 6.3: Update All Sleeplock Call Sites

**Search pattern:**
```bash
grep -r "initsleeplock" kernel/
```

**Files to update:**
- `kernel/fs/fs.c` - Per-inode sleeplocks (~NINODE calls)
- `kernel/fs/bio.c` - Per-buffer sleeplocks (if present)
- Any other subsystems using sleeplocks

**Updates needed:**
```c
// OLD
initsleeplock(&inode->lock, "inode");

// NEW
initsleeplock(&inode->lock, "inode", LOCK_LEVEL_FILESYSTEM + 1);
```

### 6.4: Testing

**Unit tests:**
- Sleeplock acquire/release basic test
- DAG ordering validation (cache lock → sleeplock)
- Multi-thread sleeplock contention

**Integration test:**
- File I/O operations (read/write/create)
- Verify no DAG violations

**Deliverables:**
- ✅ Updated sleeplock.h structure
- ✅ DAG-integrated sleeplock.c
- ✅ All call sites updated
- ✅ Tests passing

---

## Phase 7: Lock Migration Strategy

**Goal:** Migrate remaining kernel locks to modern primitives

**Estimated Effort:** 4-6 hours
**Risk:** High (filesystem is critical)

### 7.1: Lock Inventory Automation

**Script:** `scripts/lock_inventory.py`

```python
#!/usr/bin/env python3
import re
import os
from pathlib import Path

def find_locks(kernel_dir):
    locks = []
    for path in Path(kernel_dir).rglob("*.c"):
        with open(path) as f:
            content = f.read()
            # Find struct spinlock declarations
            for match in re.finditer(r'struct spinlock\s+(\w+)', content):
                locks.append({
                    'name': match.group(1),
                    'type': 'spinlock',
                    'file': str(path),
                    'recommended': 'qspinlock',
                    'line': content[:match.start()].count('\n') + 1
                })
    return locks

locks = find_locks('kernel/')
print(f"Found {len(locks)} old spinlocks to migrate")
for lock in sorted(locks, key=lambda x: x['file']):
    print(f"{lock['file']}:{lock['line']} - {lock['name']}")
```

**Run:**
```bash
cd /home/user/exov6
python3 scripts/lock_inventory.py > docs/LOCK_MIGRATION_INVENTORY.txt
```

### 7.2: Priority Matrix

**P0: Critical (Already Done ✅)**
- ptable.lock (scheduler)
- kmem.lock (memory allocator)
- cons.lock (console)

**P1: High Priority (Phase 7.4)**
- icache.lock (inode cache)
- bcache.lock (buffer cache)
- fs_log.lock (filesystem log)

**P2: Medium Priority (Phase 7.5)**
- idelock (IDE disk)
- uart.lock (serial port, if exists)

**P3: Low Priority (Phase 7.6)**
- Any remaining legacy locks

### 7.3: P1 Filesystem Lock Migration

**Estimated:** 3-4 hours

#### 7.3.1: Inode Cache Lock

**File:** `kernel/fs/fs.c`

```c
// Update structure
struct {
  struct qspinlock lock;  // Was: struct spinlock
  struct inode inode[NINODE];
} icache;

// Update init
void iinit(void) {
  qspin_init(&icache.lock, "icache", LOCK_LEVEL_FILESYSTEM);

  for (int i = 0; i < NINODE; i++) {
    initsleeplock(&icache.inode[i].lock, "inode", LOCK_LEVEL_FILESYSTEM + 1);
  }
}

// Update all acquire/release calls (automated with sed)
```

#### 7.3.2: Buffer Cache Lock

**File:** `kernel/fs/bio.c`

```c
struct {
  struct qspinlock lock;   // Main cache lock
  struct buf buf[NBUF];
  struct qspinlock rlock;  // RCU lock
  struct buf head;
} bcache;

void binit(void) {
  qspin_init(&bcache.lock, "bcache", LOCK_LEVEL_FILESYSTEM);
  qspin_init(&bcache.rlock, "bcache_rcu", LOCK_LEVEL_FILESYSTEM);
  // ...
}
```

#### 7.3.3: Filesystem Log Lock

**File:** `kernel/fs/log.c`

```c
struct log {
  struct adaptive_mutex lock;  // Better for log contention
  // ... rest of fields
};

void initlog(int dev) {
  adaptive_mutex_init(&fs_log.lock, "fs_log", LOCK_LEVEL_FILESYSTEM);
  // ...
}
```

**Migration script:**
```bash
# Automated migration
cd kernel/fs
sed -i 's/acquire(&icache\.lock)/qspin_lock(\&icache.lock)/g' fs.c
sed -i 's/release(&icache\.lock)/qspin_unlock(\&icache.lock)/g' fs.c
# ... similar for bcache
```

### 7.4: P2 Device Lock Migration

**File:** `kernel/fs/ide.c`

```c
static struct qspinlock idelock;

void ideinit(void) {
  qspin_init(&idelock, "ide", LOCK_LEVEL_DEVICE);
  // ...
}
```

### 7.5: Verification

**After each migration:**
1. Compile kernel
2. Boot in QEMU
3. Run file I/O stress test
4. Check for DAG violations
5. Performance benchmark

**Deliverables:**
- ✅ All P1 locks migrated
- ✅ All P2 locks migrated
- ✅ Lock inventory complete
- ✅ No DAG violations

---

## Phase 8: Real-World Validation

**Goal:** Validate the modern lock subsystem under real-world conditions

**Estimated Effort:** 3-4 hours
**Risk:** Medium (unpredictable workload behavior)

### 8.1: QEMU Boot Validation

**Test:** Boot kernel with DAG enabled

```bash
cd /home/user/exov6/build
cmake .. -DUSE_DAG_CHECKING=ON -DDAG_PANIC_ON_VIOLATION=ON
make kernel

qemu-system-x86_64 \
  -kernel kernel/kernel \
  -serial mon:stdio \
  -nographic \
  -smp 4 \
  -m 512M
```

**Expected:**
- ✅ Kernel boots successfully
- ✅ DAG initialization banner prints
- ✅ All CPUs come online
- ✅ No DAG violations during boot
- ✅ Shell prompt appears

**Success criteria:**
```
DAG lock ordering: ENABLED
Panic on violation: YES
cpu0: starting
cpu1: starting
cpu2: starting
cpu3: starting
init: starting sh
$
```

### 8.2: Stress Testing

**Test Suite Location:** `user/stresstest/`

#### 8.2.1: Fork/Exec Bomb

**File:** `user/stresstest/forkbomb.c`

```c
// Creates 1000 processes to stress scheduler lock
void forkbomb(int depth) {
  if (depth <= 0) return;
  for (int i = 0; i < 10; i++) {
    int pid = fork();
    if (pid == 0) {
      forkbomb(depth - 1);
      exit(0);
    }
  }
  while (wait() > 0);
}

int main(void) {
  forkbomb(3);
  exit(0);
}
```

**Expected:**
- ✅ All processes created successfully
- ✅ No ptable.lock violations
- ✅ No deadlocks
- ✅ Clean shutdown

#### 8.2.2: File I/O Storm

**File:** `user/stresstest/iostorm.c`

```c
// Stress filesystem locks
void file_io_storm(void) {
  char buf[512];
  for (int i = 0; i < 1000; i++) {
    int fd = open("testfile", O_CREATE | O_WRONLY);
    write(fd, buf, sizeof(buf));
    close(fd);

    fd = open("testfile", O_RDONLY);
    read(fd, buf, sizeof(buf));
    close(fd);

    unlink("testfile");
  }
}
```

**Expected:**
- ✅ All I/O operations complete
- ✅ No icache/bcache violations
- ✅ Correct sleeplock ordering
- ✅ No data corruption

#### 8.2.3: Multi-CPU Scheduler Stress

**File:** `user/stresstest/schedstress.c`

```c
// Stress ptable.lock with heavy context switching
void cpu_hog(void) {
  for (volatile int i = 0; i < 1000000; i++);
}

int main(void) {
  for (int i = 0; i < 100; i++) {
    if (fork() == 0) {
      cpu_hog();
      exit(0);
    }
  }
  while (wait() > 0);
  exit(0);
}
```

**Expected:**
- ✅ All processes complete
- ✅ No scheduler violations
- ✅ Fair CPU distribution

### 8.3: Performance Profiling

**Metrics:**

| Workload | Metric | Target |
|----------|--------|--------|
| **Fork/exec** | ops/sec | No regression |
| **File I/O** | ops/sec | No regression |
| **Context switch** | latency | No regression |
| **Lock acquisition** | latency | < 100 cycles |

**Profiling script:**
```bash
#!/bin/bash
# Run each stress test and collect metrics
for test in forkbomb iostorm schedstress; do
  echo "=== Testing $test ==="
  time ./$test
  dmesg | grep "DAG" | tail -20
done
```

### 8.4: DAG Statistics Analysis

**After stress tests, dump DAG stats:**

```c
// In kernel
dag_dump_stats();
```

**Expected output:**
```
=== DAG Lock Ordering Statistics ===
Total acquisitions:    1,234,567
DAG checks:            1,234,567
Violations detected:   0
Max chain length:      8
Violations by level:   [all zeros]
```

**Success criteria:**
- ✅ Violations detected: 0
- ✅ Max chain length: < 16
- ✅ All stress tests pass

**Deliverables:**
- ✅ QEMU boot successful
- ✅ All stress tests passing
- ✅ Zero DAG violations
- ✅ Performance benchmarks collected
- ✅ Statistics analyzed

---

## Phase 9: Developer Documentation

**Goal:** Comprehensive documentation for ExoV6 developers

**Estimated Effort:** 2-3 hours
**Risk:** Low (documentation only)

### 9.1: Lock Subsystem Developer Guide

**File:** `docs/LOCK_SUBSYSTEM_DEVELOPER_GUIDE.md`

**Contents:** (~3,000 lines)

1. **Introduction**
   - Overview of modern lock subsystem
   - Why we modernized
   - When to use each lock type

2. **Lock Type Selection Guide**
   - Decision tree (flowchart)
   - Lock type reference table
   - Performance characteristics

3. **DAG Lock Ordering**
   - Lock hierarchy levels
   - How to assign levels
   - Common patterns
   - Common pitfalls

4. **API Reference**
   - qspinlock API
   - adaptive_mutex API
   - LWKT token API
   - sleeplock API

5. **Code Examples**
   - Correct patterns
   - Incorrect patterns (what not to do)
   - Multi-lock scenarios

6. **Debugging DAG Violations**
   - Interpreting violation reports
   - Common violation scenarios
   - How to fix them

### 9.2: Migration Guide

**File:** `docs/LOCK_MIGRATION_GUIDE.md`

**Contents:**

1. **Migration Checklist**
   - Step-by-step process
   - Validation steps

2. **Automated Migration Script**
   ```python
   # scripts/migrate_lock.py
   # Automates spinlock → qspinlock migration
   ```

3. **Before/After Examples**
   - Real code examples
   - Common scenarios

4. **Testing Migrated Code**
   - Build with DAG enabled
   - Run stress tests
   - Check for violations

### 9.3: Performance Tuning Guide

**File:** `docs/LOCK_PERFORMANCE_TUNING.md`

**Contents:**

1. **Lock Granularity**
   - Fine-grained vs coarse-grained
   - Trade-offs

2. **Lock-Free Alternatives**
   - When to use atomics
   - Examples

3. **Reducing Critical Section Size**
   - Best practices
   - Code examples

4. **Batch Operations**
   - Amortizing lock overhead

5. **Profiling Tools**
   - How to use lock profiling
   - Interpreting results

### 9.4: API Reference Card

**File:** `docs/LOCK_API_QUICK_REFERENCE.md`

**Quick reference for developers:**

```markdown
# Lock API Quick Reference

## QSpinlock
- `qspin_init(lock, name, dag_level)` - Initialize
- `qspin_lock(lock)` - Acquire
- `qspin_unlock(lock)` - Release
- `qspin_trylock(lock)` - Try acquire (returns 0/1)
- Use for: < 100 cycle critical sections

## Adaptive Mutex
- `adaptive_mutex_init(mutex, name, dag_level)` - Initialize
- `adaptive_mutex_lock(mutex)` - Acquire
- `adaptive_mutex_unlock(mutex)` - Release
- Use for: Medium critical sections (< 10μs)

## LWKT Token
- `token_init(token, name, dag_level)` - Initialize
- `token_acquire(token)` - Acquire
- `token_release(token)` - Release
- `token_release_all()` - Release all on CPU
- Use for: CPU-local serialization

## Sleeplock
- `initsleeplock(lk, name, dag_level)` - Initialize
- `acquiresleep(lk)` - Acquire (may sleep)
- `releasesleep(lk)` - Release
- Use for: Long critical sections with I/O
```

**Deliverables:**
- ✅ Developer guide (3,000 lines)
- ✅ Migration guide with scripts
- ✅ Performance tuning guide
- ✅ API quick reference
- ✅ Code examples repository

---

## Cross-Phase Success Criteria

### Technical Criteria

- ✅ All kernel locks migrated to modern primitives
- ✅ Zero DAG violations in normal operation
- ✅ Performance equal or better than old locks
- ✅ Kernel boots successfully with DAG enabled
- ✅ All stress tests passing

### Documentation Criteria

- ✅ Comprehensive developer guide
- ✅ Migration automation scripts
- ✅ Performance tuning guide
- ✅ API reference documentation
- ✅ Code examples

### Process Criteria

- ✅ Systematic migration (inventory → priority → execute)
- ✅ Thorough testing at each step
- ✅ Performance benchmarking
- ✅ Clean git history with detailed commits

---

## Risk Mitigation

### Risk 1: Filesystem Instability

**Mitigation:**
- Migrate one lock at a time
- Test after each migration
- Keep old locks during transition
- Rollback capability

**Contingency:**
- Revert to old locks if issues
- Add more logging
- Reduce DAG strictness (warning mode)

### Risk 2: Performance Regression

**Mitigation:**
- Benchmark before/after each migration
- Use profiling to identify hotspots
- Optimize critical paths

**Contingency:**
- Fine-tune lock granularity
- Consider lock-free alternatives
- Adjust DAG overhead (conditional compilation)

### Risk 3: DAG False Positives

**Mitigation:**
- Careful lock level assignment
- Review all multi-lock patterns
- Extensive testing

**Contingency:**
- Adjust lock levels
- Add exceptions for valid patterns
- Warning mode for investigation

---

## Timeline

**Phase 6: Sleeplock Modernization**
- Estimated: 2-3 hours
- Deliverables: DAG-integrated sleeplocks

**Phase 7: Lock Migration**
- Estimated: 4-6 hours
- Deliverables: All locks migrated

**Phase 8: Real-World Validation**
- Estimated: 3-4 hours
- Deliverables: Boot test + stress tests passing

**Phase 9: Developer Documentation**
- Estimated: 2-3 hours
- Deliverables: Comprehensive docs

**Total: 11-16 hours**

---

## Execution Strategy

### Sequential Execution (Recommended)

1. **Phase 6 first** - Foundation for sleeplocks
2. **Phase 7 next** - Migrate remaining locks
3. **Phase 8 validation** - Ensure everything works
4. **Phase 9 documentation** - Share knowledge

### Parallel Opportunities

- Documentation can be written in parallel with testing
- Migration scripts can be developed early
- Stress tests can be prepared while migrating

### Checkpoints

**After Phase 6:**
- ✅ Sleeplocks use DAG
- ✅ Inode locks validated

**After Phase 7:**
- ✅ All locks migrated
- ✅ Build successful

**After Phase 8:**
- ✅ Kernel boots
- ✅ Stress tests pass

**After Phase 9:**
- ✅ Docs complete
- ✅ Project done

---

## Success Metrics

| Metric | Target | Measurement |
|--------|--------|-------------|
| **Migrations complete** | 100% | Lock inventory vs migrated |
| **DAG violations** | 0 | Stress test results |
| **Boot success** | 100% | QEMU boot test |
| **Performance regression** | < 5% | Benchmark comparison |
| **Test coverage** | 100% | All subsystems tested |
| **Documentation** | Comprehensive | Developer feedback |

---

## Conclusion

Phases 6-9 complete the lock subsystem modernization:
- **Phase 6**: DAG integration for sleeplocks
- **Phase 7**: Complete migration
- **Phase 8**: Real-world validation
- **Phase 9**: Knowledge transfer

**Ready to execute!** 🚀

---

**Next Action:** Begin Phase 6.1 - Sleeplock structure update

**Signed:** Phases 6-9 Execution Plan
**Date:** 2025-11-17
