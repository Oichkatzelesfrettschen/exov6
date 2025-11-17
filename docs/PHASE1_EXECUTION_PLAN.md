# Phase 1 Execution Plan: NUMA-Aware QSpinlock
**Date:** 2025-11-17
**Status:** Step 1.1.1 COMPLETE (25% → Target: 100%)
**Timeline:** Week 1-2 of 12-week roadmap

---

## Phase 1 Overview

**Goal:** Complete, tested, benchmarked NUMA-aware qspinlock implementation

**Current Progress:** 25% (Step 1.1.1 done)
**Remaining Work:** 75% (6 steps)
**Estimated Time:** 25 hours remaining

---

## ✅ COMPLETED: Step 1.1.1 - NUMA Topology Detection (4 hours)

**What We Built:**
- Three-tiered NUMA detection strategy:
  1. ACPI SRAT parsing (placeholder for future)
  2. CPUID Extended Topology (0x1F/0x0B leaves)
  3. Heuristic fallback (8 CPUs per socket)
- CPUID wrapper for topology enumeration
- Socket/Die level detection
- Export API: `lock_get_numa_node_count()`, `lock_get_cpu_numa_node()`

**Files Modified:**
- `kernel/sync/qspinlock.c` (+160 lines)
- `include/exo_lock.h` (+8 lines)

**Validation:**
```bash
# Test QEMU NUMA configuration
qemu-system-x86_64 -smp 16,sockets=2,cores=4,threads=2 \
  -numa node,mem=2G,cpus=0-7 \
  -numa node,mem=2G,cpus=8-15
# Expected: detect 2 NUMA nodes
```

---

## 🚧 NEXT: Step 1.1.2 - Hierarchical MCS Queue (6 hours)

### Objective
Implement two-tier MCS queue that prefers local NUMA node waiters over remote, reducing inter-socket cache coherency traffic.

### Current State Analysis

**Existing qspinlock.c MCS Implementation:**
```c
struct mcs_node {
    _Atomic(struct mcs_node *) next;  // Single queue
    _Atomic uint32_t locked;
    uint32_t numa_node;
};

void qspin_lock(struct qspinlock *lock) {
    // Current: single global queue
    // All waiters treated equally
}
```

**Problem:**
- No NUMA locality awareness in queue ordering
- Remote socket waiters cause cache line bouncing
- ~50% performance penalty on multi-socket systems

### Detailed Implementation Plan

#### Task 1.1.2.1: Enhance MCS Node Structure (1 hour)

**Goal:** Add local queue pointer to mcs_node

**Changes to `include/exo_lock.h`:**
```c
struct mcs_node {
    _Atomic(struct mcs_node *) next;        // Global queue (all waiters)
    _Atomic(struct mcs_node *) local_next;  // NEW: Local NUMA queue
    _Atomic uint32_t locked;
    uint32_t numa_node;
    uint8_t is_local;  // NEW: 1 if same NUMA as lock holder
} __attribute__((aligned(64)));
```

**Why 64-byte alignment?**
- Cache line size on x86_64
- Prevents false sharing between CPUs
- Each mcs_node in own cache line

**Validation:**
```c
static_assert(sizeof(struct mcs_node) <= 64, "mcs_node too large");
```

#### Task 1.1.2.2: Modify qspin_lock() for Hierarchical Queuing (2 hours)

**Goal:** Maintain two queues during lock acquisition

**Pseudocode:**
```c
void qspin_lock(struct qspinlock *lock) {
    // Fast path (unchanged)
    if (qspin_trylock_fast(lock)) return;

    // Slow path: Get MCS node
    struct mcs_node *node = get_mcs_node(idx);
    uint32_t my_numa = get_numa_node(mycpu() - cpus);
    node->numa_node = my_numa;

    // Atomic exchange to add to tail
    uint32_t old_val = atomic_exchange(&lock->val, my_tail << 16);

    if (old_val == 0) {
        return;  // Got lock immediately
    }

    // Link into global queue
    decode_tail(old_val >> 16, &pred_cpu, &pred_idx);
    struct mcs_node *pred = &mcs_nodes[pred_cpu][pred_idx];
    atomic_store(&pred->next, node);

    // NEW: Link into local queue if predecessor is same NUMA node
    if (pred->numa_node == my_numa) {
        node->is_local = 1;
        atomic_store(&pred->local_next, node);
    } else {
        node->is_local = 0;
    }

    // Spin on locked flag (unchanged)
    while (atomic_load(&node->locked)) {
        pause();
    }
}
```

**Key Changes:**
1. Set `numa_node` on each MCS node
2. Check predecessor's NUMA node
3. If same NUMA, link via `local_next`
4. If different NUMA, only link via `next`

**Data Structure Invariant:**
```
Global queue: All waiters linked via 'next'
Local queue:  Only same-NUMA waiters linked via 'local_next'

Example with 4 waiters (nodes 0,1,2,3):
  Node 0: NUMA 0 (lock holder)
  Node 1: NUMA 0 (local)
  Node 2: NUMA 1 (remote)
  Node 3: NUMA 0 (local)

Global queue: 0 -> 1 -> 2 -> 3
Local queue:  0 -> 1 -> 3 (skips node 2)
```

#### Task 1.1.2.3: Modify qspin_unlock() for Local Preference (2 hours)

**Goal:** Wake local waiter first if available, else wake remote

**Pseudocode:**
```c
void qspin_unlock(struct qspinlock *lock) {
    mfence();

    // Fast path: no waiters
    uint32_t val = atomic_load(&lock->val);
    if (val == 1) {
        if (atomic_compare_exchange_strong(&lock->val, &expected, 0)) {
            return;
        }
    }

    // Slow path: find next waiter
    decode_tail(val >> 16, &cpu_id, &node_idx);
    struct mcs_node *node = &mcs_nodes[cpu_id][node_idx];

    // Wait for next pointer to be set
    struct mcs_node *next_global = NULL;
    while ((next_global = atomic_load(&node->next)) == NULL) {
        pause();
    }

    // NEW: Check for local waiter first
    struct mcs_node *next_local = atomic_load(&node->local_next);
    struct mcs_node *next_to_wake;

    if (next_local != NULL) {
        // Local waiter available - prefer it
        next_to_wake = next_local;
        lock->stats.local_handoff_count++;  // Statistics
    } else {
        // No local waiter - wake remote
        next_to_wake = next_global;
        lock->stats.remote_handoff_count++;  // Statistics
    }

    // Wake the chosen waiter
    atomic_store(&next_to_wake->locked, 0);

    // Free our MCS node
    atomic_store(&node->locked, 0);

    // Clear lock
    atomic_store(&lock->val, 0);
}
```

**NUMA Preference Logic:**
```
Priority 1: Local waiter (same NUMA node)
Priority 2: Remote waiter (different NUMA node)
Bias: 100% local if available (not 2:1, but always local first)
```

**Rationale for 100% local preference:**
- Cache lines stay in local socket
- Minimal inter-socket QPI/UPI traffic
- Can tune to 2:1 later if starvation issues arise

#### Task 1.1.2.4: Handle Queue Maintenance Edge Cases (1 hour)

**Goal:** Ensure local_next pointers stay consistent

**Edge Case 1: Local waiter acquired lock, but remote waiter in between**
```
Before unlock:
  Global: A -> B -> C (A=NUMA0, B=NUMA1, C=NUMA0)
  Local:  A -> C

After A unlocks and C gets lock:
  Global: C -> (B still waiting)
  Local:  C

Problem: B is orphaned in global queue
Solution: B will be woken by C when C unlocks (via global queue)
```

**Edge Case 2: All waiters are remote**
```
Holder: NUMA 0
Waiters: All NUMA 1

Local queue: empty
Global queue: has waiters

Solution: Fall back to global queue (already handled in unlock code)
```

**Edge Case 3: Concurrent queue modifications**
```
Race: Unlock happening while new waiter arrives

Solution: Atomic operations on next pointers ensure consistency
```

**Testing Strategy:**
```c
// Test 1: All local waiters
test_qspin_all_local() {
    // 8 CPUs on NUMA 0 contend for lock
    // Verify: all handoffs are local
}

// Test 2: All remote waiters
test_qspin_all_remote() {
    // Lock held by NUMA 0 CPU, waiters all NUMA 1
    // Verify: falls back to global queue
}

// Test 3: Mixed local/remote
test_qspin_mixed() {
    // Interleaved local and remote waiters
    // Verify: local waiters get priority
}
```

### Deliverables for Step 1.1.2
- [ ] Enhanced mcs_node structure with local_next
- [ ] Modified qspin_lock() with local queue linking
- [ ] Modified qspin_unlock() with local preference
- [ ] Edge case handling and validation
- [ ] Unit tests for hierarchical queue
- [ ] Documentation of queue invariants

### Files to Modify
- `include/exo_lock.h` (mcs_node structure)
- `kernel/sync/qspinlock.c` (lock/unlock functions)

### Estimated Time: 6 hours
**Breakdown:**
- Task 1.1.2.1: 1 hour (struct changes)
- Task 1.1.2.2: 2 hours (lock function)
- Task 1.1.2.3: 2 hours (unlock function)
- Task 1.1.2.4: 1 hour (edge cases)

### Success Criteria
✓ Local waiters always get priority over remote
✓ No queue corruption under concurrent access
✓ Performance improvement on multi-socket QEMU
✓ All unit tests pass

---

## 🔮 UPCOMING: Step 1.1.3 - Performance Instrumentation (3 hours)

### Objective
Add comprehensive performance counters and statistics to qspinlock for profiling and optimization.

### Detailed Implementation Plan

#### Task 1.1.3.1: Define Statistics Structure (30 minutes)

**Add to `include/exo_lock.h`:**
```c
/**
 * Per-lock qspinlock statistics
 */
struct qspin_stats {
    // Acquisition paths
    uint64_t fast_path_count;       // Uncontended acquisitions
    uint64_t slow_path_count;       // Had to queue

    // NUMA handoffs
    uint64_t local_handoff_count;   // Woke local waiter
    uint64_t remote_handoff_count;  // Woke remote waiter

    // Contention metrics
    uint64_t total_spin_cycles;     // Total TSC cycles spent spinning
    uint64_t max_spin_cycles;       // Longest spin time
    uint64_t max_queue_depth;       // Most waiters ever queued

    // Hold time metrics
    uint64_t total_hold_cycles;     // Total TSC cycles lock held
    uint64_t max_hold_cycles;       // Longest hold time
    uint64_t acquire_count;         // Total acquisitions

    // NUMA locality
    uint64_t numa_local_acquires;   // Acquired from same NUMA
    uint64_t numa_remote_acquires;  // Acquired from different NUMA
} __attribute__((aligned(64)));  // Own cache line
```

**Add to `struct qspinlock`:**
```c
struct qspinlock {
    union {
        _Atomic uint32_t val;
        // ... existing fields
    };
    struct qspin_stats stats;  // NEW
    uint64_t last_acquire_tsc; // NEW: for hold time tracking
    uint32_t last_owner_numa;  // NEW: for locality tracking
} __attribute__((aligned(128))); // Double cache line (32 + 64 bytes stats)
```

#### Task 1.1.3.2: Instrument Fast Path (30 minutes)

**Modify `qspin_trylock_fast()`:**
```c
static inline int qspin_trylock_fast(struct qspinlock *lock) {
    uint32_t expected = 0;
    if (atomic_compare_exchange_strong(&lock->val, &expected, 1)) {
        // Success - record fast path
        __sync_fetch_and_add(&lock->stats.fast_path_count, 1);
        __sync_fetch_and_add(&lock->stats.acquire_count, 1);

        lock->last_acquire_tsc = rdtsc();
        lock->last_owner_numa = get_numa_node(mycpu() - cpus);

        return 1;
    }
    return 0;
}
```

#### Task 1.1.3.3: Instrument Slow Path (1 hour)

**Modify `qspin_lock()`:**
```c
void qspin_lock(struct qspinlock *lock) {
    uint64_t start_tsc = rdtsc();

    if (qspin_trylock_fast(lock)) {
        return;  // Stats already recorded
    }

    // Slow path
    __sync_fetch_and_add(&lock->stats.slow_path_count, 1);
    __sync_fetch_and_add(&lock->stats.acquire_count, 1);

    // ... MCS queue logic

    // Track queue depth
    uint32_t queue_depth = 0;
    struct mcs_node *iter = node;
    while (iter->next != NULL) {
        queue_depth++;
        iter = iter->next;
    }

    // Update max queue depth (atomic max)
    uint64_t old_max = lock->stats.max_queue_depth;
    while (queue_depth > old_max) {
        if (__sync_bool_compare_and_swap(&lock->stats.max_queue_depth,
                                         old_max, queue_depth)) {
            break;
        }
        old_max = lock->stats.max_queue_depth;
    }

    // Spin loop with cycle tracking
    uint64_t spin_start = rdtsc();
    while (atomic_load(&node->locked)) {
        pause();
    }
    uint64_t spin_cycles = rdtsc() - spin_start;

    // Update spin statistics
    __sync_fetch_and_add(&lock->stats.total_spin_cycles, spin_cycles);

    // Update max spin time (atomic max)
    old_max = lock->stats.max_spin_cycles;
    while (spin_cycles > old_max) {
        if (__sync_bool_compare_and_swap(&lock->stats.max_spin_cycles,
                                         old_max, spin_cycles)) {
            break;
        }
        old_max = lock->stats.max_spin_cycles;
    }

    // Record acquisition
    lock->last_acquire_tsc = rdtsc();

    uint32_t my_numa = get_numa_node(mycpu() - cpus);
    lock->last_owner_numa = my_numa;

    // Track NUMA locality
    if (my_numa == lock->last_owner_numa) {
        __sync_fetch_and_add(&lock->stats.numa_local_acquires, 1);
    } else {
        __sync_fetch_and_add(&lock->stats.numa_remote_acquires, 1);
    }
}
```

#### Task 1.1.3.4: Instrument Release Path (30 minutes)

**Modify `qspin_unlock()`:**
```c
void qspin_unlock(struct qspinlock *lock) {
    // Track hold time
    uint64_t hold_cycles = rdtsc() - lock->last_acquire_tsc;
    __sync_fetch_and_add(&lock->stats.total_hold_cycles, hold_cycles);

    // Update max hold time
    uint64_t old_max = lock->stats.max_hold_cycles;
    while (hold_cycles > old_max) {
        if (__sync_bool_compare_and_swap(&lock->stats.max_hold_cycles,
                                         old_max, hold_cycles)) {
            break;
        }
        old_max = lock->stats.max_hold_cycles;
    }

    mfence();

    // ... existing unlock logic

    // Handoff statistics already tracked in Step 1.1.2.3
}
```

#### Task 1.1.3.5: Add Statistics Reporting (30 minutes)

**New function in `kernel/sync/qspinlock.c`:**
```c
/**
 * Print qspinlock statistics
 */
void qspin_dump_stats(struct qspinlock *lock, const char *name) {
    struct qspin_stats *s = &lock->stats;

    cprintf("=== QSpinlock Stats: %s ===\n", name);
    cprintf("Acquisitions:\n");
    cprintf("  Total:        %llu\n", s->acquire_count);
    cprintf("  Fast path:    %llu (%.1f%%)\n",
            s->fast_path_count,
            100.0 * s->fast_path_count / s->acquire_count);
    cprintf("  Slow path:    %llu (%.1f%%)\n",
            s->slow_path_count,
            100.0 * s->slow_path_count / s->acquire_count);

    cprintf("\nNUMA Handoffs:\n");
    cprintf("  Local:        %llu (%.1f%%)\n",
            s->local_handoff_count,
            100.0 * s->local_handoff_count /
                    (s->local_handoff_count + s->remote_handoff_count));
    cprintf("  Remote:       %llu (%.1f%%)\n",
            s->remote_handoff_count,
            100.0 * s->remote_handoff_count /
                    (s->local_handoff_count + s->remote_handoff_count));

    cprintf("\nContention:\n");
    cprintf("  Max queue:    %llu waiters\n", s->max_queue_depth);
    cprintf("  Avg spin:     %llu cycles\n",
            s->slow_path_count > 0 ?
                s->total_spin_cycles / s->slow_path_count : 0);
    cprintf("  Max spin:     %llu cycles\n", s->max_spin_cycles);

    cprintf("\nHold Time:\n");
    cprintf("  Avg hold:     %llu cycles\n",
            s->acquire_count > 0 ?
                s->total_hold_cycles / s->acquire_count : 0);
    cprintf("  Max hold:     %llu cycles\n", s->max_hold_cycles);

    cprintf("\nNUMA Locality:\n");
    cprintf("  Local acq:    %llu (%.1f%%)\n",
            s->numa_local_acquires,
            100.0 * s->numa_local_acquires / s->acquire_count);
    cprintf("  Remote acq:   %llu (%.1f%%)\n",
            s->numa_remote_acquires,
            100.0 * s->numa_remote_acquires / s->acquire_count);
}

/**
 * Reset qspinlock statistics
 */
void qspin_reset_stats(struct qspinlock *lock) {
    memset(&lock->stats, 0, sizeof(struct qspin_stats));
}
```

#### Task 1.1.3.6: Global Lock Statistics (30 minutes)

**Add to `kernel/sync/qspinlock.c`:**
```c
/**
 * Global lock statistics aggregator
 */
struct lock_global_stats lock_stats = {0};

/**
 * Aggregate statistics from all qspinlocks
 */
void qspin_aggregate_stats(void) {
    // Placeholder - would iterate over all registered locks
    // and sum their statistics into lock_stats
    cprintf("Global lock statistics aggregation not yet implemented\n");
}

/**
 * Print global lock statistics
 */
void lock_print_stats(void) {
    cprintf("=== Global Lock Statistics ===\n");
    cprintf("Total acquires:     %llu\n", lock_stats.total_acquires);
    cprintf("Total contentions:  %llu\n", lock_stats.total_contentions);
    cprintf("Total resurrections:%llu\n", lock_stats.total_resurrections);
    cprintf("DAG violations:     %llu\n", lock_stats.total_dag_violations);
}
```

### Deliverables for Step 1.1.3
- [ ] qspin_stats structure defined
- [ ] Fast path instrumented
- [ ] Slow path instrumented (spin cycles, queue depth)
- [ ] Release path instrumented (hold time)
- [ ] Statistics reporting functions
- [ ] Global aggregation infrastructure
- [ ] Documentation of all metrics

### Files to Modify
- `include/exo_lock.h` (qspin_stats structure)
- `kernel/sync/qspinlock.c` (instrumentation code)

### Estimated Time: 3 hours

### Success Criteria
✓ All statistics accurately tracked
✓ No performance regression (< 1% overhead)
✓ Statistics report useful insights
✓ Can identify contention hotspots

---

## ⚡ THEN: Step 1.1.4 - Optimize Fast Path (4 hours)

### Objective
Achieve < 10 cycle uncontended lock acquisition through aggressive optimization.

### Current Fast Path Analysis

**Baseline:**
```c
static inline int qspin_trylock_fast(struct qspinlock *lock) {
    uint32_t expected = 0;
    return atomic_compare_exchange_strong(&lock->val, &expected, 1);
}
```

**Cycle Count Breakdown:**
```
Instruction                   Cycles (approx)
────────────────────────────────────────────
mov $0, %eax                  0.25  (part of CAS)
mov $1, %edx                  0.25  (part of CAS)
lock cmpxchg %edx, (%rdi)     ~10   (atomic CAS)
sete %al                      0.25
Total:                        ~11 cycles
```

**Target: < 10 cycles**

### Optimization Strategy

#### Task 1.1.4.1: Profile Current Fast Path (1 hour)

**Goal:** Establish accurate baseline

**Profiling Code:**
```c
// test_qspin_fast_path.c
void profile_fast_path(void) {
    struct qspinlock lock;
    qspin_init(&lock);

    uint64_t total_cycles = 0;
    const int iterations = 1000000;

    for (int i = 0; i < iterations; i++) {
        uint64_t start = rdtsc();
        qspin_lock(&lock);
        qspin_unlock(&lock);
        uint64_t end = rdtsc();

        total_cycles += (end - start);
    }

    cprintf("Average fast path: %llu cycles\n",
            total_cycles / iterations);
}
```

**Expected Baseline:** 15-20 cycles (including unlock)
**Target:** < 10 cycles (lock + unlock)

#### Task 1.1.4.2: Aggressive Inlining (30 minutes)

**Apply `__always_inline`:**
```c
static __always_inline int qspin_trylock_fast(struct qspinlock *lock) {
    uint32_t expected = 0;
    return atomic_compare_exchange_strong_explicit(
        &lock->val, &expected, 1,
        memory_order_acquire,
        memory_order_relaxed
    );
}

static __always_inline void qspin_unlock_fast(struct qspinlock *lock) {
    atomic_store_explicit(&lock->val, 0, memory_order_release);
}
```

**Why `__always_inline`?**
- Eliminates function call overhead (~5 cycles)
- Allows compiler to optimize in context
- Critical for fast path performance

#### Task 1.1.4.3: Branch Prediction Hints (30 minutes)

**Add `likely()`/`unlikely()` macros:**
```c
#define likely(x)   __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

void qspin_lock(struct qspinlock *lock) {
    if (likely(qspin_trylock_fast(lock))) {
        return;  // Fast path - most common
    }

    // Slow path - unlikely
    qspin_lock_slow(lock);
}
```

**Impact:** ~1-2 cycles from better branch prediction

#### Task 1.1.4.4: Cache Line Alignment (30 minutes)

**Ensure lock structure is cache-aligned:**
```c
struct qspinlock {
    union {
        _Atomic uint32_t val;
        // ...
    };
    struct qspin_stats stats;
} __attribute__((aligned(64)));  // Cache line aligned
```

**Create aligned lock array:**
```c
// For global locks
struct qspinlock locks[NUM_LOCKS] __attribute__((aligned(64)));
```

**Impact:** ~1-2 cycles from avoiding false sharing

#### Task 1.1.4.5: Memory Barrier Optimization (1 hour)

**Use weakest necessary memory ordering:**
```c
// Acquire lock
static __always_inline int qspin_trylock_fast(struct qspinlock *lock) {
    uint32_t expected = 0;
    // Use acquire ordering (not seq_cst)
    return atomic_compare_exchange_strong_explicit(
        &lock->val, &expected, 1,
        memory_order_acquire,    // Success: acquire barrier
        memory_order_relaxed     // Failure: no barrier needed
    );
}

// Release lock
static __always_inline void qspin_unlock_fast(struct qspinlock *lock) {
    // Use release ordering (not seq_cst)
    atomic_store_explicit(&lock->val, 0, memory_order_release);
}
```

**Why this matters:**
- `memory_order_seq_cst`: Full fence (~10 cycles)
- `memory_order_acquire`: Load fence (~2 cycles)
- `memory_order_release`: Store fence (~2 cycles)
- Savings: ~6-8 cycles

**Correctness:**
- Acquire ensures subsequent reads see lock-protected data
- Release ensures previous writes visible to next acquirer
- No need for full sequential consistency

#### Task 1.1.4.6: Assembly Optimization (1 hour)

**Hand-optimized x86_64 assembly for critical path:**
```asm
# qspin_trylock_fast_asm
# Input: %rdi = lock pointer
# Output: %rax = 1 (success), 0 (failure)
.global qspin_trylock_fast_asm
.align 16  # Align to 16-byte boundary
qspin_trylock_fast_asm:
    xor %eax, %eax              # expected = 0
    mov $1, %edx                # desired = 1
    lock cmpxchg %edx, (%rdi)   # Atomic CAS
    setz %al                    # Set return value
    ret

# qspin_unlock_fast_asm
# Input: %rdi = lock pointer
.global qspin_unlock_fast_asm
.align 16
qspin_unlock_fast_asm:
    movl $0, (%rdi)             # Store release (no lock prefix needed)
    ret
```

**Why assembly?**
- Explicit control over instruction selection
- Avoid compiler-generated prologues/epilogues
- Tightest possible code

**Usage in C:**
```c
extern int qspin_trylock_fast_asm(struct qspinlock *lock);
extern void qspin_unlock_fast_asm(struct qspinlock *lock);

void qspin_lock(struct qspinlock *lock) {
#ifdef USE_ASM_FASTPATH
    if (likely(qspin_trylock_fast_asm(lock))) {
        return;
    }
#else
    if (likely(qspin_trylock_fast(lock))) {
        return;
    }
#endif
    qspin_lock_slow(lock);
}
```

#### Task 1.1.4.7: Final Profiling and Tuning (30 minutes)

**Re-run profiling:**
```c
profile_fast_path();
// Target: < 10 cycles average
```

**If still > 10 cycles, investigate:**
```bash
# Use perf to find bottlenecks
perf record -e cycles ./qspin_benchmark
perf report

# Check assembly output
objdump -d kernel/sync/qspinlock.o | less
```

**Potential additional optimizations:**
- Prefetch lock cache line
- Use PAUSE instruction in spin loop
- Experiment with lock-free algorithms for uncontended case

### Deliverables for Step 1.1.4
- [ ] Baseline performance profile
- [ ] Aggressive inlining applied
- [ ] Branch prediction hints
- [ ] Cache line alignment
- [ ] Memory barrier optimization
- [ ] Assembly fast path (optional)
- [ ] Final performance < 10 cycles
- [ ] Performance report document

### Files to Modify/Create
- `kernel/sync/qspinlock.c` (optimizations)
- `kernel/sync/qspinlock.S` (assembly, optional)
- `kernel/arch_x86_64.h` (likely/unlikely macros)

### Estimated Time: 4 hours

### Success Criteria
✓ Uncontended acquire+release < 10 cycles
✓ No functional regression
✓ Benchmarks show improvement
✓ Code remains maintainable

---

## 🔧 INTEGRATION: Step 1.2.1 - Build System Integration (2 hours)

### Objective
Integrate qspinlock into kernel build system with feature flags.

### Task 1.2.1.1: Update CMakeLists.txt (1 hour)

**File:** `kernel/sync/CMakeLists.txt`

```cmake
# Sync subsystem sources
set(SYNC_SOURCES
    spinlock.c      # Legacy ticket spinlock
    sleeplock.c     # Sleep locks
    rcu.c           # RCU
)

# Optional: New exolock subsystem
option(CONFIG_EXOLOCK "Enable new exolock subsystem" ON)
option(CONFIG_EXOLOCK_QSPIN "Enable NUMA-aware qspinlock" ON)

if(CONFIG_EXOLOCK AND CONFIG_EXOLOCK_QSPIN)
    list(APPEND SYNC_SOURCES qspinlock.c)

    # Optional assembly optimizations
    if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64")
        option(CONFIG_EXOLOCK_QSPIN_ASM "Use assembly fast path" OFF)
        if(CONFIG_EXOLOCK_QSPIN_ASM)
            list(APPEND SYNC_SOURCES qspinlock.S)
            add_definitions(-DUSE_ASM_FASTPATH)
        endif()
    endif()

    add_definitions(-DCONFIG_EXOLOCK_QSPIN)
endif()

# Add sync library
add_library(sync ${SYNC_SOURCES})
target_include_directories(sync PUBLIC ${CMAKE_SOURCE_DIR}/include)
```

**Top-level CMakeLists.txt:**
```cmake
# Add sync subdirectory
add_subdirectory(kernel/sync)

# Link sync library to kernel
target_link_libraries(kernel sync)
```

### Task 1.2.1.2: Feature Flag Conditional Compilation (30 minutes)

**In `include/exo_lock.h`:**
```c
#ifdef CONFIG_EXOLOCK_QSPIN
    // QSpinlock API available
    void qspin_lock(struct qspinlock *lock);
    void qspin_unlock(struct qspinlock *lock);
    // ...
#else
    // Fallback to legacy spinlock
    #warning "QSpinlock not enabled, using legacy spinlock"
#endif
```

### Task 1.2.1.3: Test Build Configurations (30 minutes)

**Test all configurations:**
```bash
# Configuration 1: All disabled
cmake -DCONFIG_EXOLOCK=OFF ../
ninja kernel
./test_build

# Configuration 2: QSpinlock enabled, no assembly
cmake -DCONFIG_EXOLOCK=ON -DCONFIG_EXOLOCK_QSPIN=ON \
      -DCONFIG_EXOLOCK_QSPIN_ASM=OFF ../
ninja kernel
./test_build

# Configuration 3: Full optimizations
cmake -DCONFIG_EXOLOCK=ON -DCONFIG_EXOLOCK_QSPIN=ON \
      -DCONFIG_EXOLOCK_QSPIN_ASM=ON ../
ninja kernel
./test_build
```

### Deliverables for Step 1.2.1
- [ ] CMakeLists.txt updated
- [ ] Feature flags working
- [ ] All configurations build cleanly
- [ ] No warnings or errors

### Estimated Time: 2 hours

---

## ✅ TESTING: Step 1.2.2 - Unit Tests (6 hours)

### Objective
Comprehensive unit test suite for qspinlock correctness.

### Test Framework Setup

**File:** `tests/lock_tests.c`

```c
#include "exo_lock.h"
#include "test_framework.h"

int tests_passed = 0;
int tests_failed = 0;

#define TEST(name) void test_##name(void)
#define RUN_TEST(name) do { \
    cprintf("Running test: %s...", #name); \
    test_##name(); \
    cprintf(" PASS\n"); \
    tests_passed++; \
} while(0)

#define ASSERT(cond) do { \
    if (!(cond)) { \
        cprintf("FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        tests_failed++; \
        return; \
    } \
} while(0)
```

### Test Suite

#### Test 1: Basic Acquire/Release (30 minutes)
```c
TEST(qspin_basic) {
    struct qspinlock lock;
    qspin_init(&lock);

    // Test acquire
    qspin_lock(&lock);
    ASSERT(lock.val != 0);  // Lock held

    // Test release
    qspin_unlock(&lock);
    ASSERT(lock.val == 0);  // Lock free
}
```

#### Test 2: Multiple Acquisitions (30 minutes)
```c
TEST(qspin_multiple) {
    struct qspinlock lock;
    qspin_init(&lock);

    for (int i = 0; i < 1000; i++) {
        qspin_lock(&lock);
        // Critical section
        qspin_unlock(&lock);
    }

    ASSERT(lock.val == 0);  // Lock free at end
}
```

#### Test 3: Multi-threaded Contention (2 hours)
```c
static struct qspinlock test_lock;
static int shared_counter = 0;

void thread_worker(void *arg) {
    int iterations = (int)(uint64_t)arg;

    for (int i = 0; i < iterations; i++) {
        qspin_lock(&test_lock);
        shared_counter++;  // Not atomic, protected by lock
        qspin_unlock(&test_lock);
    }
}

TEST(qspin_multithread) {
    qspin_init(&test_lock);
    shared_counter = 0;

    const int num_threads = 8;
    const int iterations_per_thread = 10000;

    // Spawn threads
    thread_t threads[num_threads];
    for (int i = 0; i < num_threads; i++) {
        threads[i] = thread_create(thread_worker,
                                   (void*)(uint64_t)iterations_per_thread);
    }

    // Wait for completion
    for (int i = 0; i < num_threads; i++) {
        thread_join(threads[i]);
    }

    // Verify
    ASSERT(shared_counter == num_threads * iterations_per_thread);
    ASSERT(test_lock.val == 0);  // Lock released
}
```

#### Test 4: NUMA Locality (1 hour)
```c
TEST(qspin_numa_locality) {
    struct qspinlock lock;
    qspin_init(&lock);
    qspin_reset_stats(&lock);

    // Pin thread to NUMA 0
    set_cpu_affinity(0);

    // Spawn workers on NUMA 0 and NUMA 1
    thread_t local_threads[4];
    thread_t remote_threads[4];

    for (int i = 0; i < 4; i++) {
        // NUMA 0 (local)
        local_threads[i] = thread_create_on_cpu(
            thread_worker, (void*)1000, i);

        // NUMA 1 (remote)
        remote_threads[i] = thread_create_on_cpu(
            thread_worker, (void*)1000, 8 + i);
    }

    // Wait for completion
    for (int i = 0; i < 4; i++) {
        thread_join(local_threads[i]);
        thread_join(remote_threads[i]);
    }

    // Verify NUMA locality preference
    uint64_t local = lock.stats.local_handoff_count;
    uint64_t remote = lock.stats.remote_handoff_count;

    // Local handoffs should dominate if implemented correctly
    ASSERT(local > remote);
    cprintf("  Local: %llu, Remote: %llu (ratio: %.2f)\n",
            local, remote, (double)local / remote);
}
```

#### Test 5: Nested Locks (1 hour)
```c
TEST(qspin_nested) {
    struct qspinlock lock1, lock2, lock3, lock4;
    qspin_init(&lock1);
    qspin_init(&lock2);
    qspin_init(&lock3);
    qspin_init(&lock4);

    // Acquire all 4 locks (uses all 4 MCS node slots)
    qspin_lock(&lock1);
    qspin_lock(&lock2);
    qspin_lock(&lock3);
    qspin_lock(&lock4);

    // Release in reverse order
    qspin_unlock(&lock4);
    qspin_unlock(&lock3);
    qspin_unlock(&lock2);
    qspin_unlock(&lock1);

    ASSERT(lock1.val == 0);
    ASSERT(lock2.val == 0);
    ASSERT(lock3.val == 0);
    ASSERT(lock4.val == 0);
}

TEST(qspin_nested_overflow) {
    struct qspinlock locks[MCS_NODES_PER_CPU + 1];

    for (int i = 0; i <= MCS_NODES_PER_CPU; i++) {
        qspin_init(&locks[i]);
    }

    // Acquire up to limit (should succeed)
    for (int i = 0; i < MCS_NODES_PER_CPU; i++) {
        qspin_lock(&locks[i]);
    }

    // This should panic (caught by test framework)
    // qspin_lock(&locks[MCS_NODES_PER_CPU]);

    // Release all
    for (int i = MCS_NODES_PER_CPU - 1; i >= 0; i--) {
        qspin_unlock(&locks[i]);
    }
}
```

#### Test 6: Statistics Accuracy (1 hour)
```c
TEST(qspin_stats) {
    struct qspinlock lock;
    qspin_init(&lock);
    qspin_reset_stats(&lock);

    // 100 fast path acquisitions
    for (int i = 0; i < 100; i++) {
        qspin_lock(&lock);
        qspin_unlock(&lock);
    }

    ASSERT(lock.stats.fast_path_count == 100);
    ASSERT(lock.stats.slow_path_count == 0);
    ASSERT(lock.stats.acquire_count == 100);

    // Force slow path with contention
    qspin_reset_stats(&lock);

    // Thread 1 holds lock
    qspin_lock(&lock);

    // Thread 2 tries to acquire (will hit slow path)
    thread_t t = thread_create(thread_worker, (void*)1);
    usleep(10000);  // Give it time to queue

    qspin_unlock(&lock);
    thread_join(t);

    ASSERT(lock.stats.slow_path_count > 0);
}
```

#### Test 7: Stress Test (30 minutes)
```c
TEST(qspin_stress) {
    struct qspinlock lock;
    qspin_init(&lock);

    const int num_threads = 16;
    const int iterations = 1000000;

    thread_t threads[num_threads];
    for (int i = 0; i < num_threads; i++) {
        threads[i] = thread_create(thread_worker,
                                   (void*)(uint64_t)iterations);
    }

    for (int i = 0; i < num_threads; i++) {
        thread_join(threads[i]);
    }

    qspin_dump_stats(&lock, "stress_test");

    ASSERT(lock.val == 0);
    ASSERT(lock.stats.acquire_count == num_threads * iterations);
}
```

### Test Runner

```c
int main(void) {
    cprintf("=== QSpinlock Unit Tests ===\n\n");

    RUN_TEST(qspin_basic);
    RUN_TEST(qspin_multiple);
    RUN_TEST(qspin_multithread);
    RUN_TEST(qspin_numa_locality);
    RUN_TEST(qspin_nested);
    RUN_TEST(qspin_stats);
    RUN_TEST(qspin_stress);

    cprintf("\n=== Test Results ===\n");
    cprintf("Passed: %d\n", tests_passed);
    cprintf("Failed: %d\n", tests_failed);

    return tests_failed > 0 ? 1 : 0;
}
```

### Deliverables for Step 1.2.2
- [ ] Test framework setup
- [ ] 7 comprehensive unit tests
- [ ] All tests pass
- [ ] Test coverage > 90%

### Estimated Time: 6 hours

---

## 📊 BENCHMARKING: Step 1.2.3 - Microbenchmarks (4 hours)

### Objective
Measure and compare qspinlock performance against legacy spinlock.

### Benchmark Suite

#### Benchmark 1: Uncontended Throughput (1 hour)

**File:** `benchmarks/lockbench_uncontended.c`

```c
void bench_uncontended(void) {
    struct qspinlock qlock;
    struct spinlock slock;

    qspin_init(&qlock);
    initlock(&slock, "bench");

    const int iterations = 10000000;
    uint64_t start, end;

    // QSpinlock
    start = rdtsc();
    for (int i = 0; i < iterations; i++) {
        qspin_lock(&qlock);
        qspin_unlock(&qlock);
    }
    end = rdtsc();
    double qspin_cycles = (double)(end - start) / iterations;

    // Legacy spinlock
    start = rdtsc();
    for (int i = 0; i < iterations; i++) {
        acquire(&slock);
        release(&slock);
    }
    end = rdtsc();
    double spin_cycles = (double)(end - start) / iterations;

    cprintf("Uncontended Lock/Unlock:\n");
    cprintf("  QSpinlock:       %.2f cycles/op\n", qspin_cycles);
    cprintf("  Legacy spinlock: %.2f cycles/op\n", spin_cycles);
    cprintf("  Speedup:         %.2fx\n", spin_cycles / qspin_cycles);
}
```

#### Benchmark 2: 2-CPU Ping-Pong (1 hour)

```c
static struct qspinlock pingpong_qlock;
static struct spinlock pingpong_slock;
static volatile int pingpong_counter;

void pingpong_worker_qspin(void *arg) {
    int iterations = (int)(uint64_t)arg;

    for (int i = 0; i < iterations; i++) {
        qspin_lock(&pingpong_qlock);
        pingpong_counter++;
        qspin_unlock(&pingpong_qlock);
    }
}

void bench_pingpong(void) {
    const int iterations = 1000000;

    // QSpinlock
    qspin_init(&pingpong_qlock);
    pingpong_counter = 0;

    uint64_t start = rdtsc();
    thread_t t1 = thread_create_on_cpu(pingpong_worker_qspin,
                                       (void*)(uint64_t)iterations, 0);
    thread_t t2 = thread_create_on_cpu(pingpong_worker_qspin,
                                       (void*)(uint64_t)iterations, 1);
    thread_join(t1);
    thread_join(t2);
    uint64_t end = rdtsc();

    double qspin_cycles = (double)(end - start) / (iterations * 2);

    // Legacy spinlock
    initlock(&pingpong_slock, "pingpong");
    pingpong_counter = 0;

    start = rdtsc();
    // ... same test with legacy spinlock

    cprintf("2-CPU Ping-Pong:\n");
    cprintf("  QSpinlock:       %.2f cycles/op\n", qspin_cycles);
    cprintf("  Legacy spinlock: %.2f cycles/op\n", spin_cycles);
    cprintf("  Speedup:         %.2fx\n", spin_cycles / qspin_cycles);
}
```

#### Benchmark 3: N-CPU Contention (1 hour)

```c
void bench_contention(int num_threads) {
    struct qspinlock qlock;
    qspin_init(&qlock);
    qspin_reset_stats(&qlock);

    const int iterations_per_thread = 100000;

    uint64_t start = rdtsc();
    thread_t threads[num_threads];
    for (int i = 0; i < num_threads; i++) {
        threads[i] = thread_create(
            thread_worker,
            (void*)(uint64_t)iterations_per_thread);
    }
    for (int i = 0; i < num_threads; i++) {
        thread_join(threads[i]);
    }
    uint64_t end = rdtsc();

    double cycles_per_op = (double)(end - start) /
                          (num_threads * iterations_per_thread);

    cprintf("%d-CPU Contention:\n", num_threads);
    cprintf("  Cycles/op: %.2f\n", cycles_per_op);
    cprintf("  Throughput: %.2f Mops/s\n",
            (double)(num_threads * iterations_per_thread) /
            ((end - start) / tsc_frequency_mhz));

    qspin_dump_stats(&qlock, "contention");
}

void bench_all_contention(void) {
    bench_contention(1);
    bench_contention(2);
    bench_contention(4);
    bench_contention(8);
    bench_contention(16);
}
```

#### Benchmark 4: NUMA Local vs Remote (1 hour)

```c
void bench_numa_locality(void) {
    struct qspinlock lock;
    qspin_init(&lock);
    qspin_reset_stats(&lock);

    // Hold lock on NUMA 0 CPU
    set_cpu_affinity(0);

    const int iterations = 100000;

    // Local acquisitions (NUMA 0)
    uint64_t start = rdtsc();
    for (int i = 0; i < iterations; i++) {
        qspin_lock(&lock);
        qspin_unlock(&lock);
    }
    uint64_t end = rdtsc();
    double local_cycles = (double)(end - start) / iterations;

    // Remote acquisitions (NUMA 1)
    set_cpu_affinity(8);  // NUMA 1

    start = rdtsc();
    for (int i = 0; i < iterations; i++) {
        qspin_lock(&lock);
        qspin_unlock(&lock);
    }
    end = rdtsc();
    double remote_cycles = (double)(end - start) / iterations;

    cprintf("NUMA Locality:\n");
    cprintf("  Local acquire:  %.2f cycles\n", local_cycles);
    cprintf("  Remote acquire: %.2f cycles\n", remote_cycles);
    cprintf("  Penalty:        %.1f%%\n",
            100.0 * (remote_cycles - local_cycles) / local_cycles);
}
```

### Benchmark Runner

```c
int main(void) {
    cprintf("=== QSpinlock Microbenchmarks ===\n\n");

    bench_uncontended();
    bench_pingpong();
    bench_all_contention();
    bench_numa_locality();

    return 0;
}
```

### Deliverables for Step 1.2.3
- [ ] 4 comprehensive microbenchmarks
- [ ] Performance comparison vs legacy spinlock
- [ ] NUMA locality measurements
- [ ] CSV output for graphing
- [ ] Benchmark report document

### Estimated Time: 4 hours

---

## 📋 Phase 1 Final Deliverables Checklist

- [ ] Complete NUMA-aware qspinlock implementation
- [ ] Hierarchical MCS queue (local vs remote)
- [ ] Performance instrumentation
- [ ] Fast path < 10 cycles
- [ ] Build system integration
- [ ] Unit test suite (all passing)
- [ ] Microbenchmark suite
- [ ] Performance report
- [ ] Documentation complete
- [ ] Code committed and pushed
- [ ] Phase 1 report document

---

## 📈 Success Metrics

### Performance
- ✓ Uncontended acquire+release: < 10 cycles
- ✓ 2-CPU contention: < 200 cycles/op
- ✓ 8-CPU contention: < 400 cycles/op
- ✓ NUMA local preference: > 80%
- ✓ Speedup vs legacy: > 2x on contended workloads

### Quality
- ✓ All unit tests pass (0 failures)
- ✓ No memory leaks (valgrind clean)
- ✓ No data races (tsan clean)
- ✓ Code coverage > 90%

### Documentation
- ✓ All functions documented (Doxygen)
- ✓ API clearly defined
- ✓ Examples provided
- ✓ Performance report complete

---

## ⏱️ Time Tracking

| Step    | Task                        | Estimated | Actual | Status |
|---------|-----------------------------|-----------
|--------|--------|
| 1.1.1   | NUMA topology detection     | 4h        | 4h     | ✅     |
| 1.1.2   | Hierarchical MCS queue      | 6h        | —      | ⬜     |
| 1.1.3   | Performance instrumentation | 3h        | —      | ⬜     |
| 1.1.4   | Optimize fast path          | 4h        | —      | ⬜     |
| 1.2.1   | Build system integration    | 2h        | —      | ⬜     |
| 1.2.2   | Unit tests                  | 6h        | —      | ⬜     |
| 1.2.3   | Microbenchmarks             | 4h        | —      | ⬜     |
| **TOTAL** | **Phase 1**               | **29h**   | **4h** | **14%** |

---

## 🚀 Ready to Execute!

Phase 1 is fully scoped with granular tasks. Each step has:
- ✓ Clear objective
- ✓ Detailed implementation plan
- ✓ Task breakdown with time estimates
- ✓ Success criteria
- ✓ Validation strategy

**Next Immediate Action:** Begin Step 1.1.2 (Hierarchical MCS Queue)

**Estimated Completion:** Week 2 of 12-week roadmap
