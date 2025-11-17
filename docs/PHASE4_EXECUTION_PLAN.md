# Phase 4 Execution Plan: DAG Integration for Deadlock Prevention

**Timeline:** Weeks 7-8
**Objective:** Implement hierarchical lock ordering via Directed Acyclic Graph (DAG) to prevent deadlocks
**Status:** 🚀 Ready to execute

---

## Overview

DAG (Directed Acyclic Graph) integration provides compile-time and runtime deadlock prevention by enforcing hierarchical lock ordering. Every lock is assigned a level in the DAG, and locks must always be acquired in increasing order.

**Key Innovation:** Unified DAG across ALL lock types (qspinlock, adaptive_mutex, lwkt_token)

**Example Hierarchy:**
```
Level 0: Scheduler locks
Level 1: Process table locks
Level 2: Memory management locks
Level 3: File descriptor locks
Level 4: IPC queue locks
Level 5: Capability table locks
```

**Rule:** If holding lock at level N, can only acquire locks at level > N

---

## Phase 4 Architecture

### Core Components

1. **Lock Hierarchy Definition**
   - Compile-time DAG level assignment
   - Named lock classes (e.g., LOCK_CLASS_SCHED, LOCK_CLASS_PROC)
   - Runtime level validation

2. **Per-Thread Lock Tracking**
   - Thread-local lock acquisition history
   - Stack of held locks with levels
   - Maximum depth tracking (16 locks)

3. **DAG Validation Engine**
   - Check acquisition order at runtime
   - Detect circular dependencies
   - Report violations with stack trace

4. **Integration Hooks**
   - Hook into qspinlock, adaptive_mutex, lwkt_token
   - Minimal overhead when DAG checking disabled
   - Compile-time feature flag (USE_DAG_CHECKING)

5. **Violation Reporting**
   - Panic on DAG violation (debug builds)
   - Warning + statistics (production builds)
   - Detailed diagnostics (lock names, levels, acquisition order)

---

## Detailed Task Breakdown

### Step 4.1: Data Structures (Day 1)

#### Task 4.1.1: Define lock hierarchy levels

**File:** `include/exo_lock.h`

```c
/* Lock hierarchy levels (DAG ordering) */
#define LOCK_LEVEL_NONE         0   // No ordering requirement
#define LOCK_LEVEL_SCHEDULER    10  // Scheduler internal locks
#define LOCK_LEVEL_PROCESS      20  // Process table, thread management
#define LOCK_LEVEL_MEMORY       30  // Page tables, allocators
#define LOCK_LEVEL_VFS          40  // File system metadata
#define LOCK_LEVEL_IPC          50  // IPC queues, pipes
#define LOCK_LEVEL_CAPABILITY   60  // Capability tables
#define LOCK_LEVEL_DEVICE       70  // Device drivers
#define LOCK_LEVEL_USER         80  // User-visible resources
#define LOCK_LEVEL_MAX          100 // Maximum level

/* Lock classes (for named categories) */
enum lock_class {
    LOCK_CLASS_NONE = 0,
    LOCK_CLASS_SCHED,
    LOCK_CLASS_PROC,
    LOCK_CLASS_MEM,
    LOCK_CLASS_VFS,
    LOCK_CLASS_IPC,
    LOCK_CLASS_CAP,
    LOCK_CLASS_DEV,
    LOCK_CLASS_USER,
};

/* Map lock classes to DAG levels */
extern const uint32_t lock_class_levels[];
```

#### Task 4.1.2: Define per-thread lock tracking

**File:** `include/exo_lock.h`

```c
#define MAX_HELD_LOCKS 16

/* Per-lock acquisition record */
struct lock_acquisition {
    void *lock_addr;           // Address of lock
    const char *lock_name;     // Debug name
    uint32_t dag_level;        // DAG level at acquisition
    uint32_t lock_type;        // LOCK_TYPE_QSPIN, ADAPTIVE, TOKEN
    uint64_t acquire_tsc;      // Acquisition timestamp
    const char *file;          // Source location
    int line;
} __attribute__((aligned(64)));

/* Per-thread lock tracking */
struct thread_lock_tracker {
    struct lock_acquisition stack[MAX_HELD_LOCKS];
    uint32_t depth;            // Current stack depth
    uint32_t max_depth;        // Maximum depth reached
    uint32_t violations;       // DAG violations detected
    uint32_t highest_level;    // Highest DAG level held
} __attribute__((aligned(128)));

/* Get current thread's lock tracker */
extern struct thread_lock_tracker *get_lock_tracker(void);
```

#### Task 4.1.3: Define DAG validation statistics

**File:** `include/exo_lock.h`

```c
/* Global DAG statistics */
struct dag_stats {
    _Atomic uint64_t total_acquisitions;
    _Atomic uint64_t dag_checks;
    _Atomic uint64_t violations_detected;
    _Atomic uint64_t violations_by_level[LOCK_LEVEL_MAX];
    _Atomic uint64_t max_chain_length;
} __attribute__((aligned(128)));

extern struct dag_stats global_dag_stats;
```

---

### Step 4.2: Core DAG Implementation (Days 2-3)

#### Task 4.2.1: Implement lock tracking

**File:** `kernel/sync/dag.c`

```c
/**
 * Track lock acquisition in DAG
 *
 * Called by all lock types on successful acquisition
 */
void dag_lock_acquired(void *lock_addr, const char *name,
                      uint32_t dag_level, uint32_t lock_type,
                      const char *file, int line) {
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker) return;  // Not tracking (e.g., early boot)

    // Check for stack overflow
    if (tracker->depth >= MAX_HELD_LOCKS) {
        panic("dag_lock_acquired: lock stack overflow (max %d)", MAX_HELD_LOCKS);
    }

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

    // Update statistics
    if (tracker->depth > tracker->max_depth) {
        tracker->max_depth = tracker->depth;
    }

    if (dag_level > tracker->highest_level) {
        tracker->highest_level = dag_level;
    }

    __sync_fetch_and_add(&global_dag_stats.total_acquisitions, 1);
}
```

#### Task 4.2.2: Implement DAG validation

**File:** `kernel/sync/dag.c`

```c
/**
 * Validate DAG ordering before lock acquisition
 *
 * Returns 1 if acquisition is safe, 0 if would violate DAG
 */
int dag_validate_acquisition(void *lock_addr, const char *name,
                             uint32_t dag_level, uint32_t lock_type,
                             const char *file, int line) {
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker) return 1;  // No tracking active

    __sync_fetch_and_add(&global_dag_stats.dag_checks, 1);

    // Check if already holding this lock (reacquisition)
    for (uint32_t i = 0; i < tracker->depth; i++) {
        if (tracker->stack[i].lock_addr == lock_addr) {
            // Reacquisition of same lock is OK for LWKT tokens
            if (lock_type == LOCK_TYPE_TOKEN) {
                return 1;
            }

            // Error for other lock types
            panic("dag_validate: reacquisition of non-token lock %s at %s:%d",
                  name, file, line);
        }
    }

    // Check DAG ordering: new lock must be at higher level than all held locks
    for (uint32_t i = 0; i < tracker->depth; i++) {
        if (dag_level <= tracker->stack[i].dag_level) {
            // DAG VIOLATION!
            __sync_fetch_and_add(&global_dag_stats.violations_detected, 1);
            __sync_fetch_and_add(&global_dag_stats.violations_by_level[dag_level], 1);

            dag_report_violation(tracker, lock_addr, name, dag_level,
                               lock_type, file, line);

            return 0;  // Violation detected
        }
    }

    return 1;  // Acquisition is safe
}
```

#### Task 4.2.3: Implement lock release tracking

**File:** `kernel/sync/dag.c`

```c
/**
 * Track lock release in DAG
 *
 * Called by all lock types on release
 */
void dag_lock_released(void *lock_addr) {
    struct thread_lock_tracker *tracker = get_lock_tracker();

    if (!tracker || tracker->depth == 0) return;

    // Find lock in stack (should be at top for proper nesting)
    for (int i = tracker->depth - 1; i >= 0; i--) {
        if (tracker->stack[i].lock_addr == lock_addr) {
            // Found it - remove from stack

            if (i != (int)(tracker->depth - 1)) {
                // Not at top - improper nesting (warning only)
                cprintf("WARNING: Non-LIFO lock release: %s (depth %d, expected %d)\n",
                       tracker->stack[i].lock_name, i, tracker->depth - 1);
            }

            // Shift stack down
            for (uint32_t j = i; j < tracker->depth - 1; j++) {
                tracker->stack[j] = tracker->stack[j + 1];
            }

            tracker->depth--;

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

    // Lock not found in stack (could be released via token_release_all)
    // This is OK - just ignore
}
```

#### Task 4.2.4: Implement violation reporting

**File:** `kernel/sync/dag.c`

```c
/**
 * Report DAG violation with detailed diagnostics
 */
static void dag_report_violation(struct thread_lock_tracker *tracker,
                                void *new_lock, const char *new_name,
                                uint32_t new_level, uint32_t new_type,
                                const char *file, int line) {
    cprintf("\n=== DAG VIOLATION DETECTED ===\n");
    cprintf("Attempted acquisition:\n");
    cprintf("  Lock:   %s (%p)\n", new_name, new_lock);
    cprintf("  Level:  %u\n", new_level);
    cprintf("  Type:   %s\n", lock_type_name(new_type));
    cprintf("  Source: %s:%d\n", file, line);

    cprintf("\nCurrently held locks:\n");
    for (uint32_t i = 0; i < tracker->depth; i++) {
        struct lock_acquisition *acq = &tracker->stack[i];
        cprintf("  [%u] %s (level %u) at %s:%d\n",
               i, acq->lock_name, acq->dag_level, acq->file, acq->line);
    }

    cprintf("\nViolation: Level %u <= %u (must be strictly increasing)\n",
           new_level, tracker->highest_level);

    tracker->violations++;

#ifdef DAG_PANIC_ON_VIOLATION
    panic("DAG violation - deadlock risk");
#endif
}
```

---

### Step 4.3: Lock Type Integration (Day 4)

#### Task 4.3.1: Integrate with qspinlock

**File:** `kernel/sync/qspinlock.c`

Add DAG hooks:

```c
void qspin_lock(struct qspinlock *lock) {
#ifdef USE_DAG_CHECKING
    if (!dag_validate_acquisition(lock, lock->name, lock->dag_level,
                                  LOCK_TYPE_QSPIN, __FILE__, __LINE__)) {
        // Violation detected
        return;  // Or panic depending on config
    }
#endif

    // ... existing acquisition logic ...

#ifdef USE_DAG_CHECKING
    dag_lock_acquired(lock, lock->name, lock->dag_level,
                     LOCK_TYPE_QSPIN, __FILE__, __LINE__);
#endif
}

void qspin_unlock(struct qspinlock *lock) {
#ifdef USE_DAG_CHECKING
    dag_lock_released(lock);
#endif

    // ... existing release logic ...
}
```

#### Task 4.3.2: Integrate with adaptive_mutex

**File:** `kernel/sync/adaptive_mutex.c`

```c
void adaptive_mutex_lock(struct adaptive_mutex *mutex) {
#ifdef USE_DAG_CHECKING
    if (!dag_validate_acquisition(mutex, mutex->name, mutex->dag_level,
                                  LOCK_TYPE_ADAPTIVE, __FILE__, __LINE__)) {
        return;
    }
#endif

    // ... existing acquisition logic ...

#ifdef USE_DAG_CHECKING
    dag_lock_acquired(mutex, mutex->name, mutex->dag_level,
                     LOCK_TYPE_ADAPTIVE, __FILE__, __LINE__);
#endif
}
```

#### Task 4.3.3: Integrate with lwkt_token

**File:** `kernel/sync/lwkt_token.c`

```c
void token_acquire(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;
    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);

    // Fast path: reacquisition
    if (likely(owner == my_cpu)) {
        __sync_fetch_and_add(&token->stats.reacquire_count, 1);
        return;  // No DAG check needed for reacquisition
    }

#ifdef USE_DAG_CHECKING
    // Only validate on first acquisition
    if (!dag_validate_acquisition(token, token->name, token->dag_level,
                                  LOCK_TYPE_TOKEN, __FILE__, __LINE__)) {
        return;
    }
#endif

    // ... existing acquisition logic ...

#ifdef USE_DAG_CHECKING
    dag_lock_acquired(token, token->name, token->dag_level,
                     LOCK_TYPE_TOKEN, __FILE__, __LINE__);
#endif
}
```

---

### Step 4.4: Per-Thread Tracking (Day 5)

#### Task 4.4.1: Thread structure integration

**File:** `include/proc.h`

```c
struct proc {
    // ... existing fields ...

#ifdef USE_DAG_CHECKING
    struct thread_lock_tracker lock_tracker;  // DAG tracking
#endif
};
```

#### Task 4.4.2: Implement tracker accessor

**File:** `kernel/sync/dag.c`

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

#### Task 4.4.3: Initialize tracker on thread creation

**File:** `kernel/proc.c`

```c
// In allocproc() or thread creation
#ifdef USE_DAG_CHECKING
    memset(&p->lock_tracker, 0, sizeof(p->lock_tracker));
#endif
```

---

### Step 4.5: Testing and Validation (Days 6-7)

#### Task 4.5.1: Unit tests

**File:** `kernel/sync/test_dag.c`

Test cases:
1. Proper ordering (should succeed)
2. Reverse ordering (should detect violation)
3. Reacquisition (tokens should allow, others should fail)
4. Lock release tracking
5. Stack overflow detection
6. Multi-level chains (depth 8+)
7. Concurrent DAG validation
8. Statistics accuracy

#### Task 4.5.2: Integration tests

**File:** `kernel/sync/test_dag_integration.c`

Test DAG across all three lock types:
1. Mixed lock acquisition (qspin → adaptive → token)
2. Proper level progression
3. Violation detection across types
4. token_release_all() interaction with DAG

#### Task 4.5.3: Benchmarks

**File:** `kernel/sync/bench_dag.c`

Measure overhead:
1. DAG validation latency (< 20 cycles target)
2. Lock acquisition with DAG vs without
3. Stack tracking overhead
4. Statistics update overhead

---

### Step 4.6: Build Integration (Day 7)

#### Task 4.6.1: CMake configuration

**File:** `kernel/CMakeLists.txt`

```cmake
# DAG deadlock prevention
option(USE_DAG_CHECKING "Enable DAG lock ordering checks" OFF)

if(USE_DAG_CHECKING)
    target_compile_definitions(kernel PRIVATE USE_DAG_CHECKING)
    message(STATUS "  - DAG checking: ENABLED")
else()
    message(STATUS "  - DAG checking: DISABLED")
endif()

# Add DAG source
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/dag.c")
    list(APPEND SYNC_SOURCES sync/dag.c)
endif()
```

#### Task 4.6.2: Panic-on-violation option

```cmake
option(DAG_PANIC_ON_VIOLATION "Panic on DAG violations (vs warning)" ON)

if(DAG_PANIC_ON_VIOLATION AND USE_DAG_CHECKING)
    target_compile_definitions(kernel PRIVATE DAG_PANIC_ON_VIOLATION)
endif()
```

---

### Step 4.7: Documentation (Day 8)

#### Task 4.7.1: Design documentation

**File:** `docs/DAG_DESIGN.md`

Sections:
- DAG hierarchy overview
- Lock level assignment guidelines
- Integration with lock types
- Performance characteristics
- Debugging DAG violations

#### Task 4.7.2: API documentation

**File:** `docs/DAG_API.md`

Functions:
- `dag_validate_acquisition()`
- `dag_lock_acquired()`
- `dag_lock_released()`
- `dag_dump_stats()`

#### Task 4.7.3: Completion report

**File:** `docs/PHASE4_COMPLETION_REPORT.md`

---

## Performance Targets

| Metric | Target | Rationale |
|--------|--------|-----------|
| DAG validation overhead | < 20 cycles | Minimal impact on lock acquisition |
| Stack depth | 16 locks | Sufficient for kernel call chains |
| Memory overhead | < 2KB per thread | Acceptable for tracker structure |
| Violation detection rate | 100% | Must catch all ordering issues |

---

## Example Usage

### Lock Definition

```c
// Process table lock (level 20)
struct qspinlock proc_table_lock;
qspin_init(&proc_table_lock, "proc_table", LOCK_LEVEL_PROCESS);

// Memory allocator lock (level 30)
struct adaptive_mutex kalloc_mutex;
adaptive_mutex_init(&kalloc_mutex, "kalloc", LOCK_LEVEL_MEMORY, 0);

// Capability table lock (level 60)
struct lwkt_token *cap_token = token_pool_get(cap_table);
// Token inherits level from initialization
```

### Proper Acquisition Order

```c
// CORRECT: Acquire in increasing order
qspin_lock(&proc_table_lock);           // Level 20
adaptive_mutex_lock(&kalloc_mutex);     // Level 30
token_acquire(cap_token);               // Level 60

// ... critical section ...

token_release(cap_token);
adaptive_mutex_unlock(&kalloc_mutex);
qspin_unlock(&proc_table_lock);
```

### DAG Violation Example

```c
// INCORRECT: Would trigger DAG violation
adaptive_mutex_lock(&kalloc_mutex);     // Level 30
qspin_lock(&proc_table_lock);           // Level 20 < 30 - VIOLATION!

// Output:
// === DAG VIOLATION DETECTED ===
// Attempted acquisition:
//   Lock:   proc_table (0xffff8000...)
//   Level:  20
//   Type:   qspinlock
//   Source: proc.c:123
//
// Currently held locks:
//   [0] kalloc (level 30) at kalloc.c:45
//
// Violation: Level 20 <= 30 (must be strictly increasing)
// PANIC: DAG violation - deadlock risk
```

---

## Validation Criteria

### Correctness ✅
- [ ] Detects all DAG violations
- [ ] No false positives
- [ ] Proper token reacquisition handling
- [ ] Stack tracking accurate

### Performance ✅
- [ ] < 20 cycles validation overhead
- [ ] Minimal memory footprint
- [ ] No impact when disabled (compile-time)

### Integration ✅
- [ ] Works with all 3 lock types
- [ ] Clean build with feature flags
- [ ] Thread tracker initialization correct

### Testing ✅
- [ ] 10+ unit tests passing
- [ ] Integration tests covering mixed locks
- [ ] Benchmarks showing overhead

---

## Success Metrics

- **Code:** ~600 lines (dag.c implementation)
- **Tests:** ~800 lines (unit + integration tests)
- **Docs:** ~500 lines (design + API + report)
- **Commits:** ~4 commits
- **All tests:** PASSING ✅
- **Overhead:** < 20 cycles ✅

---

**Status:** Ready to execute
**Next Action:** Begin Task 4.1.1 (Define lock hierarchy levels)
