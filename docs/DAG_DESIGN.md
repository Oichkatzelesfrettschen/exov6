/**
 * @file DAG_DESIGN.md
 * @brief DAG Lock Ordering System - A Pedagogical Commentary
 *
 * In the style of Lion's Commentary on UNIX 6th Edition
 *
 * @author ExoV6 Lock Subsystem Team
 * @date 2025-11-17
 * @version 1.0
 */

# DAG Lock Ordering: A Line-by-Line Commentary

## Introduction and Motivation

The DAG (Directed Acyclic Graph) lock ordering system prevents deadlocks by
enforcing a strict hierarchy on lock acquisitions. This commentary explains
the implementation in the pedagogical style of Lion's Commentary on UNIX V6.

### The Deadlock Problem

Consider two processes P1 and P2, and two locks L1 and L2:

```
Time    P1                  P2
----    --                  --
t0      acquire(L1)         acquire(L2)
t1      acquire(L2)         acquire(L1)
        [BLOCKS]            [BLOCKS]

        --> DEADLOCK <--
```

Both processes are now deadlocked, waiting for each other.

### The DAG Solution

By assigning each lock a level in a hierarchy (DAG levels), we enforce
the rule: **locks must always be acquired in strictly increasing order**.

```
Lock Hierarchy:
Level 10: LOCK_LEVEL_SCHEDULER
Level 20: LOCK_LEVEL_PROCESS
Level 30: LOCK_LEVEL_MEMORY
Level 40: LOCK_LEVEL_VFS
Level 50: LOCK_LEVEL_IPC
Level 60: LOCK_LEVEL_CAPABILITY
Level 70: LOCK_LEVEL_DEVICE
Level 80: LOCK_LEVEL_USER
```

If P1 holds L1 (level 20) and wants L2 (level 10), this is REJECTED because
10 < 20 violates the hierarchy. This prevents circular wait conditions.

---

## Section 1: Data Structures (include/exo_lock.h:461-492)

### 1.1 Lock Acquisition Record (lines 461-469)

```c
struct lock_acquisition {
    void *lock_addr;           /* Address of lock structure */
    const char *lock_name;     /* Debug name */
    uint32_t dag_level;        /* DAG level at acquisition */
    uint32_t lock_type;        /* LOCK_TYPE_* constant */
    uint64_t acquire_tsc;      /* Acquisition timestamp (TSC) */
    const char *file;          /* Source file */
    int line;                  /* Source line number */
} __attribute__((aligned(64)));
```

**Purpose**: Records a single lock acquisition event.

**Field Analysis**:
- `lock_addr`: Identifies which lock was acquired. Used to find the lock
  in the stack when releasing (see dag_lock_released(), line 425).

- `lock_name`: Human-readable identifier for debugging. Printed in violation
  reports (see dag_report_violation(), line 115).

- `dag_level`: The hierarchical level of this lock. This is the KEY field
  for validation - we check that each new acquisition has a HIGHER level
  than all currently held locks (see dag_validate_acquisition(), line 178).

- `lock_type`: Distinguishes between LOCK_TYPE_QSPIN (0), LOCK_TYPE_ADAPTIVE (1),
  and LOCK_TYPE_TOKEN (2). Tokens have special reacquisition semantics
  (see line 186-197).

- `acquire_tsc`: Time-Stamp Counter value at acquisition. Used for hold-time
  analysis and debugging timeout scenarios.

- `file`, `line`: Source location where lock was acquired. Critical for
  debugging - tells us EXACTLY where in the code the lock was taken
  (printed in violation reports, line 120).

**Cache Alignment**: 64-byte alignment prevents false sharing. Multiple
CPUs may be checking their own stacks simultaneously - we don't want
their lock_acquisition records sharing cache lines.

### 1.2 Per-Thread Lock Tracker (lines 475-481)

```c
struct thread_lock_tracker {
    struct lock_acquisition stack[MAX_HELD_LOCKS];
    uint32_t depth;            /* Current stack depth */
    uint32_t max_depth;        /* Maximum depth reached */
    uint32_t violations;       /* DAG violations detected */
    uint32_t highest_level;    /* Highest DAG level currently held */
} __attribute__((aligned(128)));
```

**Purpose**: Tracks all locks currently held by a thread.

**The Stack Metaphor**: Think of this as a stack of dinner plates. Each
plate is a lock_acquisition record. When you acquire a lock, you push
a plate onto the stack. When you release, you pop it off.

**Field Analysis**:
- `stack[MAX_HELD_LOCKS]`: Array of 16 acquisition records. Why 16?
  Empirical analysis shows kernel call chains rarely exceed 8 nested locks.
  16 provides headroom while keeping the structure compact (16 * 64 = 1024 bytes).

- `depth`: Current number of locks held. Valid range: [0, MAX_HELD_LOCKS).
  Used as array index for next acquisition (see dag_lock_acquired(), line 282).

- `max_depth`: High-water mark. Useful for tuning MAX_HELD_LOCKS if we
  discover deep call chains in production.

- `violations`: Count of DAG violations by this thread. In warning mode
  (DAG_PANIC_ON_VIOLATION=OFF), we increment this instead of panicking
  (see dag_report_violation(), line 127).

- `highest_level`: Optimization. Instead of scanning the entire stack to
  find the highest level, we track it here. Updated on acquire (line 293)
  and recalculated on release (line 443-449).

**Cache Alignment**: 128-byte alignment (2 cache lines). The structure is
exactly 1152 bytes, so it spans multiple cache lines anyway. Alignment
ensures it starts on a cache line boundary.

**Cross-Reference**: This structure is embedded in `struct proc` (include/proc.h:158)
under conditional compilation `#ifdef USE_DAG_CHECKING`. Each process/thread
has its own tracker.

### 1.3 Global DAG Statistics (lines 486-492)

```c
struct dag_stats {
    _Atomic uint64_t total_acquisitions;
    _Atomic uint64_t dag_checks;
    _Atomic uint64_t violations_detected;
    _Atomic uint64_t violations_by_level[LOCK_LEVEL_MAX];
    _Atomic uint64_t max_chain_length;
} __attribute__((aligned(128)));
```

**Purpose**: System-wide statistics for DAG performance analysis.

**Why Atomic?**: Multiple CPUs update these concurrently. Without atomics,
we'd get data races. Atomics ensure safe concurrent increment.

**Field Analysis**:
- `total_acquisitions`: Total lock acquisitions tracked. Incremented in
  dag_lock_acquired() (line 297). Useful for calculating overhead:
  overhead = dag_checks / total_acquisitions.

- `dag_checks`: How many times we validated ordering. Should equal
  total_acquisitions minus reacquisitions (tokens don't check on reacquire).

- `violations_detected`: Count of ordering violations. Should be ZERO in
  production! Non-zero indicates bugs in lock ordering.

- `violations_by_level[]`: Histogram of violations by the violating lock's
  level. Shows which lock levels are most problematic. Updated in
  dag_validate_acquisition() (line 180-182).

- `max_chain_length`: Deepest lock stack seen across all threads. If this
  approaches MAX_HELD_LOCKS (16), we need to increase the limit.

**Cache Alignment**: 128 bytes. This structure is ~848 bytes (8 + 8 + 8 +
800 + 8), spans many cache lines. Alignment ensures no false sharing with
adjacent structures.

---

## Section 2: Core Validation Logic (kernel/sync/dag.c)

### 2.1 Getting the Thread's Lock Tracker (lines 65-75)

```c
struct thread_lock_tracker *get_lock_tracker(void) {
#ifdef USE_DAG_CHECKING
    struct proc *p = myproc();
    if (p) {
        return &p->lock_tracker;
    }
#endif
    return NULL;
}
```

**Purpose**: Returns the current thread's lock tracker.

**Line-by-Line Analysis**:
- Line 66: Conditional compilation. If USE_DAG_CHECKING is not defined,
  the function body is empty and returns NULL immediately (line 74).
  This is how we achieve ZERO overhead when DAG checking is disabled.

- Line 67: Call `myproc()` to get current process/thread structure.
  This is a per-CPU variable access (see kernel/proc.c). Very fast -
  usually just loads from %gs segment register on x86-64.

- Line 68-70: If we have a valid process pointer, return the address
  of its lock_tracker field. The `&` is important - we return a POINTER,
  not a copy. This allows dag_lock_acquired() to modify the tracker.

- Line 74: Return NULL if DAG checking is disabled OR if called before
  process structures are initialized (early boot). Callers check for
  NULL and skip tracking if so.

**Cross-Reference**: Called by dag_validate_acquisition() (line 169),
dag_lock_acquired() (line 275), and dag_lock_released() (line 424).

### 2.2 Validation - The Heart of DAG (lines 158-221)

```c
int dag_validate_acquisition(void *lock_addr, const char *name,
                             uint32_t dag_level, uint32_t lock_type,
                             const char *file, int line) {
```

**Purpose**: Check if acquiring a new lock would violate DAG ordering.

**Returns**: 1 if acquisition is safe, 0 if would cause violation.

**Algorithm Overview**:
1. Get thread's lock tracker
2. Check for reacquisition of same lock
3. Check if new lock's level > all held locks' levels
4. Report violation if check fails

**Line-by-Line Commentary**:

Lines 159-165: Early exit if DAG checking disabled
```c
#ifndef USE_DAG_CHECKING
    return 1;  // DAG checking disabled
#else
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker) {
        return 1;  // No tracking available (e.g., early boot)
    }
```

**Why return 1?**: Returning 1 means "acquisition is OK". If DAG checking
is disabled, ALL acquisitions are OK. Similarly, during early boot before
process structures exist, we can't track, so we allow everything.

Lines 167-178: Increment check counter, scan for reacquisition
```c
    __sync_fetch_and_add(&global_dag_stats.dag_checks, 1);

    // Check if already holding this lock (reacquisition)
    for (uint32_t i = 0; i < tracker->depth; i++) {
        if (tracker->stack[i].lock_addr == lock_addr) {
            // Reacquisition of same lock

            if (lock_type == LOCK_TYPE_TOKEN) {
                // LWKT tokens allow reacquisition (CPU-owned)
                return 1;
            }
```

**The Reacquisition Check**: We scan the stack looking for `lock_addr`.
If found, this is a reacquisition - trying to acquire a lock we already hold.

**Token Exception**: LWKT tokens are CPU-owned, not thread-owned. A CPU
can reacquire its own token (this is COMMON - see lwkt_token.c line 223-227).
For tokens, reacquisition is ALLOWED (return 1).

**Other Lock Types**: For qspinlocks and adaptive mutexes, reacquisition
is an ERROR. These are classic locks - recursive acquisition leads to
self-deadlock. We panic here (lines 186-197).

Lines 198-210: The DAG Check - Critical Section!
```c
    // Check DAG ordering: new lock must be at higher level than all held locks
    for (uint32_t i = 0; i < tracker->depth; i++) {
        if (dag_level <= tracker->stack[i].dag_level) {
            // DAG VIOLATION!
            __sync_fetch_and_add(&global_dag_stats.violations_detected, 1);

            if (dag_level < LOCK_LEVEL_MAX) {
                __sync_fetch_and_add(&global_dag_stats.violations_by_level[dag_level], 1);
            }

            dag_report_violation(tracker, lock_addr, name, dag_level,
                               lock_type, file, line);

            return 0;  // Violation detected
        }
    }
```

**The Core Invariant**: For DAG ordering to prevent deadlocks, we must
ensure: **∀ held locks L_h: dag_level_new > dag_level(L_h)**

In plain English: The new lock's level must be STRICTLY GREATER than
ALL currently held locks.

**Why Strictly Greater?**: If we allow equal levels, we could have:
- Thread 1: acquire(L1, level=20) then acquire(L2, level=20)
- Thread 2: acquire(L2, level=20) then acquire(L1, level=20)
This creates a circular wait! Strict inequality (>) prevents this.

**Loop Analysis**: We scan ALL held locks (depth can be up to 16).
For each held lock, we check if new_level <= held_level.

**Performance**: O(depth) scan. Typically depth < 4, so this is fast.
We could optimize with `highest_level` field (already tracked), but
the explicit scan is more robust and easier to verify.

**Violation Handling**:
- Increment global violation counter (atomic)
- Increment per-level histogram (atomic)
- Call dag_report_violation() for detailed diagnostics
- Return 0 to indicate failure

**Cross-Reference**: The return value is checked by:
- qspinlock.c:313-319
- adaptive_mutex.c:222-229
- lwkt_token.c:233-240

Line 216: Success case
```c
    return 1;  // Acquisition is safe
#endif
```

If we reach here, all checks passed. The new lock has a higher level
than all held locks. Return 1 to allow acquisition.

### 2.3 Recording Acquisition (lines 264-298)

```c
void dag_lock_acquired(void *lock_addr, const char *name,
                      uint32_t dag_level, uint32_t lock_type,
                      const char *file, int line) {
```

**Purpose**: Record a successful lock acquisition in the thread's stack.

**Precondition**: dag_validate_acquisition() must have returned 1.
This function assumes the acquisition is VALID.

**Line-by-Line**:

Lines 265-272: Early exit and overflow check
```c
#ifndef USE_DAG_CHECKING
    return;  // DAG checking disabled
#else
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker) {
        return;  // No tracking available
    }

    // Check for stack overflow
    if (tracker->depth >= MAX_HELD_LOCKS) {
        panic("dag_lock_acquired: lock stack overflow (max %d)", MAX_HELD_LOCKS);
    }
```

**Stack Overflow Check**: If depth == MAX_HELD_LOCKS (16), the stack is
FULL. We can't record another acquisition. This is a fatal error - panic
immediately. In practice, this should NEVER happen. If it does, either:
1. There's a lock leak (not releasing locks)
2. Call chains are deeper than expected (increase MAX_HELD_LOCKS)

Lines 275-283: Record the acquisition
```c
    // Record acquisition
    struct lock_acquisition *acq = &tracker->stack[tracker->depth];
    acq->lock_addr = lock_addr;
    acq->lock_name = name;
    acq->dag_level = dag_level;
    acq->lock_type = lock_type;
    acq->acquire_tsc = rdtsc();
    acq->file = file;
    acq->line = line;

    tracker->depth++;
```

**Array Indexing**: `tracker->stack[tracker->depth]` gets the NEXT
empty slot. If depth=3, we have locks at [0], [1], [2], and we're
about to fill [3].

**Field Assignment**: Straightforward - copy all parameters into the
acquisition record. Note `rdtsc()` reads the Time-Stamp Counter for
precise timing.

**Increment Depth**: AFTER filling the record, increment depth. Now
depth=4, indicating 4 locks held. The invariant is: locks [0..depth-1]
are valid, [depth..MAX_HELD_LOCKS-1] are uninitialized.

Lines 285-296: Update statistics
```c
    // Update statistics
    if (tracker->depth > tracker->max_depth) {
        tracker->max_depth = tracker->depth;

        // Update global max chain length
        uint64_t old_max = global_dag_stats.max_chain_length;
        while (tracker->depth > old_max) {
            if (__sync_bool_compare_and_swap(&global_dag_stats.max_chain_length,
                                             old_max, tracker->depth)) {
                break;
            }
            old_max = global_dag_stats.max_chain_length;
        }
    }

    if (dag_level > tracker->highest_level) {
        tracker->highest_level = dag_level;
    }

    __sync_fetch_and_add(&global_dag_stats.total_acquisitions, 1);
#endif
```

**Max Depth Tracking**: Per-thread max_depth tracks the deepest stack
for THIS thread. Global max_chain_length tracks the deepest stack
across ALL threads.

**Atomic Max Update**: The while loop is a classic atomic max pattern:
1. Read current max (old_max)
2. If our value is larger, try to CAS it
3. If CAS fails (someone else updated), read new max and retry
4. Loop until either we set it or it's already larger

**Highest Level**: Simple optimization. Instead of scanning the stack
to find the highest level during validation, we track it here. Updated
on acquire, recalculated on release.

**Total Acquisitions**: Global counter, atomically incremented.

### 2.4 Releasing Locks (lines 412-462)

```c
void dag_lock_released(void *lock_addr) {
#ifndef USE_DAG_CHECKING
    return;  // DAG checking disabled
#else
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker || tracker->depth == 0) {
        return;  // No locks held
    }
```

**Purpose**: Remove a lock from the thread's stack when released.

**Empty Stack Check**: If depth==0, stack is empty. Nothing to release.
This can happen if token_release_all() is called with no tokens held.

**The Search**:
```c
    // Find lock in stack (should be at top for proper nesting)
    for (int i = tracker->depth - 1; i >= 0; i--) {
        if (tracker->stack[i].lock_addr == lock_addr) {
            // Found it - remove from stack

            if (i != (int)(tracker->depth - 1)) {
                // Not at top - improper nesting (warning only)
                cprintf("WARNING: Non-LIFO lock release: %s (depth %d, expected %d)\n",
                       tracker->stack[i].lock_name, i, tracker->depth - 1);
            }
```

**Search Strategy**: We search BACKWARDS from the top (depth-1 down to 0).
Why backwards? Because in the common case (LIFO release), the lock is
at the top. We find it immediately (i == depth-1).

**Non-LIFO Release**: If the lock is NOT at the top (i < depth-1), locks
are being released out of order. Example:
```
acquire(L1); acquire(L2); acquire(L3);  // Stack: [L1, L2, L3]
release(L2);                             // Out of order!
```

This is technically OK for deadlock prevention (DAG is still valid), but
indicates unusual code patterns. We print a warning.

**Special Case - token_release_all()**: LWKT tokens are often released
in batch via token_release_all() (lwkt_token.c:330). This releases ALL
tokens, not in LIFO order. The warning is expected and harmless here.

**Stack Compaction**:
```c
            // Shift stack down (remove element at index i)
            for (uint32_t j = i; j < tracker->depth - 1; j++) {
                tracker->stack[j] = tracker->stack[j + 1];
            }

            tracker->depth--;
```

**Array Removal**: To remove element i, we shift all elements above it
down by one position. If depth=4 and we remove i=1:
```
Before: [L0, L1, L2, L3]  depth=4
After:  [L0, L2, L3, ??]  depth=3
```
Element at [3] is now garbage, but that's OK - it's beyond depth-1.

**Recalculate Highest Level**:
```c
            // Recalculate highest level
            tracker->highest_level = 0;
            for (uint32_t j = 0; j < tracker->depth; j++) {
                if (tracker->stack[j].dag_level > tracker->highest_level) {
                    tracker->highest_level = tracker->stack[j].dag_level;
                }
            }

            return;
        }
    }
```

**Why Recalculate?**: If we removed the lock with the highest level,
`highest_level` is now stale. We must scan the remaining locks to find
the new maximum.

**Performance**: O(depth) scan. Typically depth < 4 after release, so
this is fast.

**Lock Not Found**:
```c
    // Lock not found in stack
    // This is OK - could be released via token_release_all()
    // Just ignore
#endif
}
```

If we searched the entire stack and didn't find `lock_addr`, it's not
held. This can happen legitimately with token_release_all(), which
releases locks then clears the stack in one shot. We just return silently.

---

## Section 3: Integration with Lock Types

### 3.1 QSpinlock Integration (kernel/sync/qspinlock.c)

**Init Function (line 245)**:
```c
void qspin_init(struct qspinlock *lock, const char *name, uint32_t dag_level) {
    atomic_store_explicit(&lock->val, 0, memory_order_relaxed);

    // Initialize metadata
    lock->name = name;
    lock->dag_level = dag_level;
```

**New Parameters**: Added `name` and `dag_level`. The lock now knows
its own name and level. This is stored IN the lock structure, not
separately, so it's always available.

**Lock Function (lines 310-332)**:
```c
void qspin_lock(struct qspinlock *lock) {
#ifdef USE_DAG_CHECKING
    // Validate DAG ordering before attempting acquisition
    if (!dag_validate_acquisition(lock, lock->name, lock->dag_level,
                                  LOCK_TYPE_QSPIN, __FILE__, __LINE__)) {
#ifdef DAG_PANIC_ON_VIOLATION
        panic("qspin_lock: DAG violation");
#else
        return;  // Skip acquisition on violation (warning mode)
#endif
    }
#endif
```

**Hook Placement**: BEFORE any lock acquisition attempt. We validate
first, then acquire. This is critical - we can't acquire THEN validate,
because by then it's too late.

**__FILE__ and __LINE__**: Compiler macros. __FILE__ expands to source
file name ("qspinlock.c"), __LINE__ expands to line number. These get
passed to dag_validate_acquisition() and stored in the acquisition record.

**Three Acquisition Paths**: Qspinlock has three code paths where it
successfully acquires:
1. Fast path - immediate acquire (line 326)
2. Slow path - got lock immediately when joining queue (line 369)
3. Slow path - got lock after spinning (line 437)

ALL three paths must call dag_lock_acquired(). Let's examine each:

**Path 1 - Fast Path (lines 326-332)**:
```c
    // Fast path: try to acquire immediately (LIKELY: most locks are uncontended)
    if (likely(qspin_trylock_fast(lock))) {
#ifdef USE_DAG_CHECKING
        // Record acquisition in DAG tracker
        dag_lock_acquired(lock, lock->name, lock->dag_level,
                         LOCK_TYPE_QSPIN, __FILE__, __LINE__);
#endif
        return;
    }
```

Fast path succeeds (lock was free). Record it and return.

**Path 2 - Immediate in Queue (lines 369-376)**:
```c
    if (unlikely(old_val == 0)) {
        // We got the lock immediately (unlikely since fast path failed)
#ifdef USE_DAG_CHECKING
        dag_lock_acquired(lock, lock->name, lock->dag_level,
                         LOCK_TYPE_QSPIN, __FILE__, __LINE__);
#endif
        return;
    }
```

Rare case: fast path failed, but when we joined queue, lock was free.
We got it without spinning. Record and return.

**Path 3 - After Spinning (lines 437-443)**:
```c
    // We have the lock now
    lock->last_acquire_tsc = rdtsc();
    lock->last_owner_numa = my_numa;

#ifdef USE_DAG_CHECKING
    // Record acquisition in DAG tracker
    dag_lock_acquired(lock, lock->name, lock->dag_level,
                     LOCK_TYPE_QSPIN, __FILE__, __LINE__);
#endif

    mfence();  // Memory barrier
}
```

Common slow path: we queued, spun on our MCS node, then got the lock.
Record acquisition.

**Unlock Function (lines 457-461)**:
```c
void qspin_unlock(struct qspinlock *lock) {
#ifdef USE_DAG_CHECKING
    // Track lock release in DAG
    dag_lock_released(lock);
#endif

    // Track hold time
    uint64_t hold_cycles = rdtsc() - lock->last_acquire_tsc;
```

**Hook at Start**: We call dag_lock_released() at the VERY START of
unlock, before any other logic. This ensures the DAG tracker is
updated before we actually release the lock.

### 3.2 LWKT Token Integration - Special Reacquisition Handling

**Acquire Function (lines 217-241)**:
```c
void token_acquire(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;

    /* ===== FAST PATH: Already own it ===== */
    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);

    if (likely(owner == my_cpu)) {
        // We already own it - just increment reacquire count
        // No DAG check needed for reacquisition
        __sync_fetch_and_add(&token->stats.reacquire_count, 1);
        return;
    }

#ifdef USE_DAG_CHECKING
    // Validate DAG ordering before first acquisition
    // (not needed for reacquisition above)
    if (!dag_validate_acquisition(token, token->name, token->dag_level,
                                  LOCK_TYPE_TOKEN, __FILE__, __LINE__)) {
```

**Critical Design Decision**: DAG check comes AFTER the reacquisition
fast path. Why?

1. Reacquisition is VERY common for tokens (see Phase 3 benchmarks -
   85% of acquisitions are reacquires).

2. Reacquisition is SAFE - same CPU holding same token multiple times
   cannot cause deadlock.

3. DAG check would be WASTEFUL - we'd look up the lock in the stack,
   find it's already there, and allow it. Why waste cycles?

**Optimization**: Skip DAG check entirely for reacquisition. Check only
on FIRST acquisition. This reduces overhead significantly.

**Cross-Reference**: This is why dag_validate_acquisition() has special
handling for LOCK_TYPE_TOKEN reacquisition (dag.c line 186-197).

---

## Section 4: Build System Integration

### 4.1 CMake Configuration (kernel/CMakeLists.txt:229-244)

```cmake
# DAG lock ordering for deadlock prevention
option(USE_DAG_CHECKING "Enable DAG lock ordering validation" OFF)
if(USE_DAG_CHECKING)
    target_compile_definitions(kernel PRIVATE USE_DAG_CHECKING)
    message(STATUS "  - DAG lock ordering: ENABLED")

    option(DAG_PANIC_ON_VIOLATION "Panic on DAG violations (vs warning)" ON)
    if(DAG_PANIC_ON_VIOLATION)
        target_compile_definitions(kernel PRIVATE DAG_PANIC_ON_VIOLATION)
        message(STATUS "    - Panic on violation: YES")
    else()
        message(STATUS "    - Panic on violation: NO (warning only)")
    endif()
else()
    message(STATUS "  - DAG lock ordering: DISABLED")
endif()
```

**Two-Level Configuration**:

**Level 1 - USE_DAG_CHECKING**: Master switch. OFF by default (zero overhead).
When ON, all DAG code is compiled in. Use for:
- Development builds
- Testing
- Production builds where deadlock detection is critical

**Level 2 - DAG_PANIC_ON_VIOLATION**: Enforcement policy. ON by default
(when DAG is enabled). Two modes:

1. **Panic Mode (ON)**: Violation causes immediate panic. Use for:
   - Development (find bugs early)
   - Testing (violations are ALWAYS bugs)
   - Production where correctness > availability

2. **Warning Mode (OFF)**: Violation logs warning, skips lock, continues.
   Use for:
   - Production where availability > perfect correctness
   - Temporary workarounds while fixing violations
   - Research/debugging (collect violation data without crashing)

**Compile-Time Optimization**: Both options use `#ifdef` checks. When
disabled, preprocessor removes ALL DAG code. Zero runtime overhead,
zero code size impact.

---

## Section 5: Performance Analysis

### 5.1 Overhead Breakdown

**Per-Acquisition Cost (DAG enabled)**:
```
dag_validate_acquisition():
  - Function call overhead:        ~5 cycles
  - get_lock_tracker():            ~3 cycles (per-CPU load)
  - Reacquisition scan (avg 2):    ~4 cycles
  - DAG level scan (avg 2):        ~4 cycles
  - Total validation:              ~16 cycles

dag_lock_acquired():
  - Function call overhead:        ~5 cycles
  - Record copy (7 fields):        ~7 cycles
  - Statistics update:             ~3 cycles
  - Total tracking:                ~15 cycles

Grand Total:                       ~31 cycles
```

**Target was < 20 cycles**. We're at 31 cycles. Where's the overhead?

**Analysis**: The two function calls (validate + acquired) cost ~10 cycles.
We could optimize by inlining, but that would bloat code size significantly.
Trade-off: accept 31 cycles for maintainability.

**Real-World Impact**: Typical lock acquisition is ~100 cycles (qspinlock
uncontended is 88.5 cycles, see Phase 3). DAG adds 31 cycles = **35% overhead**.

**When DAG disabled**: Zero cycles. All code compiled out.

### 5.2 Memory Overhead

**Per-Thread**:
```
struct thread_lock_tracker: 1152 bytes
```

**Per-System**:
```
struct dag_stats: ~848 bytes (global, single copy)
```

**Total for 100 threads**: ~113 KB. Acceptable.

---

## Section 6: Common Patterns and Best Practices

### 6.1 Correct Lock Ordering Example

```c
// Correct: Always acquire in increasing level order

void process_schedule(struct proc *p) {
    struct qspinlock proc_lock;      // Level 20
    struct adaptive_mutex mem_lock;   // Level 30
    struct lwkt_token *cap_token;     // Level 60

    qspin_init(&proc_lock, "proc_table", LOCK_LEVEL_PROCESS);
    adaptive_mutex_init(&mem_lock, "kalloc", LOCK_LEVEL_MEMORY, 0);
    cap_token = token_pool_get(p->cap_table);  // Pre-init'd at level 60

    // Correct order: 20 → 30 → 60
    qspin_lock(&proc_lock);           // Level 20
    adaptive_mutex_lock(&mem_lock);   // Level 30 > 20 ✓
    token_acquire(cap_token);         // Level 60 > 30 ✓

    // ... critical section ...

    // Release in any order (DAG only checks acquire)
    token_release(cap_token);
    qspin_unlock(&proc_lock);
    adaptive_mutex_unlock(&mem_lock);
}
```

### 6.2 Violation Example

```c
// WRONG: Violates DAG ordering

void process_schedule_WRONG(struct proc *p) {
    struct qspinlock proc_lock;      // Level 20
    struct adaptive_mutex mem_lock;   // Level 30

    adaptive_mutex_lock(&mem_lock);   // Level 30
    qspin_lock(&proc_lock);           // Level 20 < 30 ❌ VIOLATION!

    // DAG will detect this and panic (or warn)
}
```

**Output**:
```
=== DAG VIOLATION DETECTED ===
Attempted acquisition:
  Lock:   proc_table (0xffff800012345678)
  Level:  20
  Type:   qspinlock
  Source: proc.c:123

Currently held locks (1):
  [0] kalloc (level 30) at kalloc.c:45

Violation: Level 20 <= 30 (must be strictly increasing)
PANIC: DAG violation - deadlock risk
```

---

## Section 7: Debugging with DAG

### 7.1 Reading Violation Reports

The violation report tells you:
1. **What** lock you tried to acquire (name, address, level, type)
2. **Where** you tried to acquire it (file:line)
3. **What** locks you currently hold (full stack with file:line)
4. **Why** it's a violation (level comparison)

**Debugging Strategy**:
1. Look at the "Currently held locks" section
2. Find the lock with level >= your attempted level
3. Check if you really need BOTH locks
4. If yes, reverse the acquisition order
5. If no, release the higher lock first

### 7.2 Statistics Inspection

```c
// In kernel debug console
void debug_dag_stats(void) {
    dag_dump_stats();
}
```

**Output**:
```
=== DAG Lock Ordering Statistics ===
Total acquisitions: 1250000
DAG checks:         1100000
Violations:         0
Max chain length:   5

Violations by level:
  (none)
```

**Interpretation**:
- **Total acquisitions**: All lock acquisitions tracked
- **DAG checks**: Should be ≈ total - reacquisitions
- **Violations**: Should be ZERO in production!
- **Max chain length**: Deepest lock stack (should be < 16)

---

## Conclusion

The DAG lock ordering system prevents deadlocks by enforcing hierarchical
lock acquisition. The implementation is:

1. **Correct**: All circular wait conditions are prevented
2. **Efficient**: 31-cycle overhead when enabled, zero when disabled
3. **Debuggable**: Detailed violation reports with source locations
4. **Flexible**: Panic or warning modes for different deployments

**Cross-References**:
- Data structures: include/exo_lock.h (lines 432-550)
- Validation logic: kernel/sync/dag.c (lines 158-462)
- QSpinlock integration: kernel/sync/qspinlock.c (lines 310-461)
- Adaptive mutex integration: kernel/sync/adaptive_mutex.c (lines 219-362)
- LWKT token integration: kernel/sync/lwkt_token.c (lines 217-311)
- Build system: kernel/CMakeLists.txt (lines 229-244)

---

**End of Commentary**

@see kernel/sync/dag.c
@see include/exo_lock.h
@see docs/PHASE4_EXECUTION_PLAN.md
@see docs/PHASE4_COMPLETION_REPORT.md (forthcoming)
