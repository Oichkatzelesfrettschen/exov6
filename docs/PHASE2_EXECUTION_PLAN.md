# Phase 2 Execution Plan: Adaptive Mutex Implementation

**Timeline:** Weeks 3-4
**Objective:** Implement high-performance adaptive mutex with owner-running detection and turnstile queues
**Status:** 🚀 Ready to execute

---

## Overview

Adaptive mutexes combine spinning and blocking based on lock holder state:
- **Spin** if lock holder is running (likely to release soon)
- **Block** if lock holder is sleeping/preempted (may take long)

This approach minimizes context switches for short critical sections while avoiding CPU waste for long ones.

---

## Phase 2 Architecture

### Core Components

1. **Owner Tracking**
   - Current lock holder CPU/thread ID
   - Holder's running state (on-CPU vs off-CPU)
   - Priority for priority inheritance

2. **Adaptive Spin**
   - Limited spin attempts before blocking
   - Owner-running detection
   - Exponential backoff during spin

3. **Turnstile Queues**
   - Per-mutex wait queue
   - FIFO ordering for fairness
   - Priority inheritance support

4. **Statistics & Profiling**
   - Spin vs block decision tracking
   - Average hold times
   - Contention patterns

---

## Detailed Task Breakdown

### Step 2.1: Data Structures (Week 3, Day 1)

#### Task 2.1.1: Define adaptive_mutex structure
**File:** `include/exo_lock.h`
**Lines:** ~50

```c
struct adaptive_mutex {
    _Atomic uint32_t locked;           // 0 = free, 1 = locked
    _Atomic uint32_t owner_cpu;        // CPU ID of current holder
    _Atomic uint32_t owner_tid;        // Thread ID of current holder
    struct turnstile *turnstile;       // Wait queue for blockers
    uint32_t spin_limit;               // Max spin iterations
    struct mutex_stats stats;          // Performance tracking
    const char *name;                  // Debug name
    uint32_t dag_level;                // Deadlock prevention
} __attribute__((aligned(128)));
```

**Subtasks:**
1. Define structure fields
2. Add alignment for cache efficiency
3. Document each field
4. Add compile-time assertions

#### Task 2.1.2: Define turnstile structure
**File:** `include/exo_lock.h`
**Lines:** ~30

```c
struct turnstile {
    struct thread_queue waiters;       // FIFO wait queue
    _Atomic uint32_t count;            // Number of waiters
    struct adaptive_mutex *lock;       // Associated mutex
    uint8_t priority_inherited;        // PI active flag
} __attribute__((aligned(64)));
```

**Subtasks:**
1. Design wait queue structure
2. Add priority tracking
3. Document queue semantics

#### Task 2.1.3: Define mutex statistics
**File:** `include/exo_lock.h`
**Lines:** ~20

```c
struct mutex_stats {
    uint64_t acquire_count;
    uint64_t spin_acquire_count;      // Acquired while spinning
    uint64_t block_acquire_count;     // Acquired after blocking
    uint64_t total_spin_cycles;
    uint64_t total_block_cycles;
    uint64_t max_hold_cycles;
    uint64_t contention_count;
} __attribute__((aligned(64)));
```

---

### Step 2.2: Core Operations (Week 3, Days 2-3)

#### Task 2.2.1: Implement adaptive_mutex_init()
**File:** `kernel/sync/adaptive_mutex.c`
**Lines:** ~30

**Implementation:**
```c
void adaptive_mutex_init(struct adaptive_mutex *mutex, const char *name, uint32_t dag_level) {
    atomic_store(&mutex->locked, 0);
    atomic_store(&mutex->owner_cpu, INVALID_CPU);
    atomic_store(&mutex->owner_tid, INVALID_TID);
    mutex->turnstile = turnstile_alloc(mutex);
    mutex->spin_limit = ADAPTIVE_SPIN_LIMIT;
    memset(&mutex->stats, 0, sizeof(mutex->stats));
    mutex->name = name;
    mutex->dag_level = dag_level;
}
```

**Subtasks:**
1. Initialize atomic fields
2. Allocate turnstile
3. Set default spin limit
4. Zero statistics

#### Task 2.2.2: Implement owner_is_running()
**File:** `kernel/sync/adaptive_mutex.c`
**Lines:** ~40

**Logic:**
```c
static inline bool owner_is_running(struct adaptive_mutex *mutex) {
    uint32_t owner_cpu = atomic_load(&mutex->owner_cpu);
    uint32_t owner_tid = atomic_load(&mutex->owner_tid);

    if (owner_cpu == INVALID_CPU) return false;
    if (owner_cpu >= NCPU) return false;

    // Check if owner's CPU is running the owner thread
    struct cpu *cpu = &cpus[owner_cpu];
    struct proc *running = cpu->proc;

    if (!running) return false;
    if (running->tid != owner_tid) return false;

    return true;
}
```

**Subtasks:**
1. Load owner CPU and TID atomically
2. Validate owner CPU ID
3. Check CPU's current thread
4. Return running status

#### Task 2.2.3: Implement adaptive_mutex_lock()
**File:** `kernel/sync/adaptive_mutex.c`
**Lines:** ~120

**Fast Path:**
```c
// Try immediate acquisition
uint32_t expected = 0;
if (atomic_compare_exchange_strong(&mutex->locked, &expected, 1)) {
    // Fast path success
    atomic_store(&mutex->owner_cpu, mycpu()->id);
    atomic_store(&mutex->owner_tid, mythread()->tid);
    mutex->stats.acquire_count++;
    return;
}
```

**Adaptive Spin:**
```c
uint64_t spin_start = rdtsc();
int spins = 0;

while (spins < mutex->spin_limit) {
    // Check if owner is running
    if (owner_is_running(mutex)) {
        // Spin with backoff
        for (int i = 0; i < backoff; i++) {
            pause();
        }

        // Try acquire again
        expected = 0;
        if (atomic_compare_exchange_strong(&mutex->locked, &expected, 1)) {
            // Spin succeeded
            uint64_t spin_cycles = rdtsc() - spin_start;
            mutex->stats.spin_acquire_count++;
            mutex->stats.total_spin_cycles += spin_cycles;
            set_owner(mutex);
            return;
        }

        spins++;
        backoff = min(backoff * 2, MAX_BACKOFF);
    } else {
        // Owner not running - break to block
        break;
    }
}
```

**Block Path:**
```c
// Spin failed or owner not running - block on turnstile
uint64_t block_start = rdtsc();

turnstile_wait(mutex->turnstile, mythread());

// When woken, we have the lock
uint64_t block_cycles = rdtsc() - block_start;
mutex->stats.block_acquire_count++;
mutex->stats.total_block_cycles += block_cycles;
set_owner(mutex);
```

**Subtasks:**
1. Implement fast path (uncontended CAS)
2. Implement adaptive spin loop
3. Implement turnstile blocking
4. Update statistics
5. Set owner on acquisition

#### Task 2.2.4: Implement adaptive_mutex_unlock()
**File:** `kernel/sync/adaptive_mutex.c`
**Lines:** ~60

**Implementation:**
```c
void adaptive_mutex_unlock(struct adaptive_mutex *mutex) {
    // Clear owner
    atomic_store(&mutex->owner_cpu, INVALID_CPU);
    atomic_store(&mutex->owner_tid, INVALID_TID);

    // Check for waiters
    if (turnstile_has_waiters(mutex->turnstile)) {
        // Wake next waiter
        struct thread *next = turnstile_wake_one(mutex->turnstile);

        // Transfer ownership to next waiter
        atomic_store(&mutex->owner_cpu, next->cpu->id);
        atomic_store(&mutex->owner_tid, next->tid);

        // Let next waiter take the lock (it already has it)
        return;
    }

    // No waiters - simple unlock
    atomic_store(&mutex->locked, 0);
}
```

**Subtasks:**
1. Clear current owner
2. Check turnstile for waiters
3. Wake next waiter if present
4. Transfer ownership
5. Release lock if no waiters

#### Task 2.2.5: Implement adaptive_mutex_trylock()
**File:** `kernel/sync/adaptive_mutex.c`
**Lines:** ~30

```c
int adaptive_mutex_trylock(struct adaptive_mutex *mutex) {
    uint32_t expected = 0;

    if (atomic_compare_exchange_strong(&mutex->locked, &expected, 1)) {
        set_owner(mutex);
        mutex->stats.acquire_count++;
        return 1;
    }

    return 0;
}
```

---

### Step 2.3: Turnstile Implementation (Week 3, Day 4)

#### Task 2.3.1: Implement turnstile_alloc()
**File:** `kernel/sync/turnstile.c`
**Lines:** ~40

```c
struct turnstile *turnstile_alloc(struct adaptive_mutex *mutex) {
    struct turnstile *ts = kalloc();
    if (!ts) panic("turnstile_alloc: out of memory");

    thread_queue_init(&ts->waiters);
    atomic_store(&ts->count, 0);
    ts->lock = mutex;
    ts->priority_inherited = 0;

    return ts;
}
```

#### Task 2.3.2: Implement turnstile_wait()
**File:** `kernel/sync/turnstile.c`
**Lines:** ~80

```c
void turnstile_wait(struct turnstile *ts, struct thread *thread) {
    pushcli();  // Disable interrupts

    // Add to wait queue
    thread_queue_push(&ts->waiters, thread);
    atomic_fetch_add(&ts->count, 1);

    // Set thread state to sleeping
    thread->state = SLEEPING;
    thread->wchan = ts;

    // Priority inheritance: boost lock owner priority
    if (thread->priority > ts->lock->owner_priority) {
        priority_inherit(ts->lock, thread->priority);
        ts->priority_inherited = 1;
    }

    // Release CPU and reschedule
    sched();

    // When we wake up, we have the lock
    thread->wchan = NULL;

    popcli();  // Re-enable interrupts
}
```

**Subtasks:**
1. Add thread to FIFO queue
2. Set thread state to SLEEPING
3. Implement priority inheritance
4. Call scheduler to yield CPU
5. Handle wakeup

#### Task 2.3.3: Implement turnstile_wake_one()
**File:** `kernel/sync/turnstile.c`
**Lines:** ~50

```c
struct thread *turnstile_wake_one(struct turnstile *ts) {
    struct thread *next = thread_queue_pop(&ts->waiters);

    if (!next) return NULL;

    atomic_fetch_sub(&ts->count, 1);

    // Restore priority if PI was active
    if (ts->priority_inherited) {
        priority_restore(ts->lock);
        ts->priority_inherited = 0;
    }

    // Wake the thread
    next->state = RUNNABLE;

    return next;
}
```

#### Task 2.3.4: Implement thread_queue operations
**File:** `kernel/sync/turnstile.c`
**Lines:** ~60

```c
void thread_queue_init(struct thread_queue *q) {
    q->head = NULL;
    q->tail = NULL;
}

void thread_queue_push(struct thread_queue *q, struct thread *t) {
    t->next = NULL;

    if (q->tail) {
        q->tail->next = t;
    } else {
        q->head = t;
    }

    q->tail = t;
}

struct thread *thread_queue_pop(struct thread_queue *q) {
    struct thread *t = q->head;

    if (!t) return NULL;

    q->head = t->next;

    if (!q->head) {
        q->tail = NULL;
    }

    t->next = NULL;
    return t;
}
```

---

### Step 2.4: Priority Inheritance (Week 3, Day 5)

#### Task 2.4.1: Implement priority_inherit()
**File:** `kernel/sync/priority.c`
**Lines:** ~50

```c
void priority_inherit(struct adaptive_mutex *mutex, uint32_t waiter_priority) {
    uint32_t owner_tid = atomic_load(&mutex->owner_tid);

    struct thread *owner = find_thread(owner_tid);
    if (!owner) return;

    // Boost owner priority if needed
    if (waiter_priority > owner->priority) {
        owner->effective_priority = waiter_priority;

        // Re-insert into run queue if running
        if (owner->state == RUNNABLE) {
            runqueue_update_priority(owner);
        }
    }
}
```

#### Task 2.4.2: Implement priority_restore()
**File:** `kernel/sync/priority.c`
**Lines:** ~40

```c
void priority_restore(struct adaptive_mutex *mutex) {
    uint32_t owner_tid = atomic_load(&mutex->owner_tid);

    struct thread *owner = find_thread(owner_tid);
    if (!owner) return;

    // Restore original priority
    owner->effective_priority = owner->priority;

    if (owner->state == RUNNABLE) {
        runqueue_update_priority(owner);
    }
}
```

---

### Step 2.5: Integration & Testing (Week 4, Days 1-2)

#### Task 2.5.1: Build system integration
**File:** `kernel/CMakeLists.txt`

**Add sources:**
```cmake
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/adaptive_mutex.c")
    list(APPEND SYNC_SOURCES sync/adaptive_mutex.c)
endif()
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/turnstile.c")
    list(APPEND SYNC_SOURCES sync/turnstile.c)
endif()
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/priority.c")
    list(APPEND SYNC_SOURCES sync/priority.c)
endif()
```

#### Task 2.5.2: Unit tests
**File:** `kernel/sync/test_adaptive_mutex.c`
**Lines:** ~800

**Test cases:**
1. Initialization
2. Basic lock/unlock
3. Trylock behavior
4. Adaptive spin (owner running)
5. Blocking (owner not running)
6. Priority inheritance
7. Turnstile FIFO ordering
8. Statistics tracking
9. Concurrent stress test
10. Deadlock prevention

#### Task 2.5.3: Microbenchmarks
**File:** `kernel/sync/bench_adaptive_mutex.c`
**Lines:** ~600

**Benchmarks:**
1. Uncontended latency
2. Short critical section (spin benefit)
3. Long critical section (block benefit)
4. Priority inheritance overhead
5. Throughput scaling (1-8 threads)

---

### Step 2.6: Documentation (Week 4, Day 3)

#### Task 2.6.1: Design documentation
**File:** `docs/ADAPTIVE_MUTEX_DESIGN.md`
**Lines:** ~500

**Sections:**
- Overview
- Architecture
- Owner-running detection
- Adaptive spin algorithm
- Turnstile queuing
- Priority inheritance
- Performance analysis
- Integration guide

#### Task 2.6.2: API documentation
**File:** `docs/ADAPTIVE_MUTEX_API.md`
**Lines:** ~200

**Functions:**
- `adaptive_mutex_init()`
- `adaptive_mutex_lock()`
- `adaptive_mutex_unlock()`
- `adaptive_mutex_trylock()`
- `adaptive_mutex_dump_stats()`

#### Task 2.6.3: Completion report
**File:** `docs/PHASE2_COMPLETION_REPORT.md`
**Lines:** ~400

---

## Performance Targets

| Metric | Target | Measurement |
|--------|--------|-------------|
| Uncontended latency | < 15ns | RDTSC |
| Spin success rate | > 80% (short CS) | Statistics |
| Block overhead | < 1μs | RDTSC |
| PI overhead | < 100ns | RDTSC |
| Throughput scaling | Linear to 4 CPUs | Benchmark |

---

## Validation Criteria

### Correctness
- ✅ All unit tests pass (10/10)
- ✅ No race conditions (verified with TSan)
- ✅ Proper priority inheritance
- ✅ FIFO fairness maintained

### Performance
- ✅ Faster than pure spinlock for long CS
- ✅ Faster than pure mutex for short CS
- ✅ Adaptive behavior validated

### Integration
- ✅ Clean build with -Wall -Wextra
- ✅ No memory leaks (verified with Valgrind)
- ✅ DAG integration works
- ✅ Statistics accurate

---

## Risk Mitigation

### Risk 1: Thread state tracking complexity
**Mitigation:** Simplify by using CPU's current thread pointer

### Risk 2: Priority inheritance bugs
**Mitigation:** Extensive testing, reference NetBSD implementation

### Risk 3: Performance regression
**Mitigation:** Benchmark against baseline, tune spin limits

---

## Dependencies

### Kernel Components Needed
1. Thread/process structure with TID
2. CPU structure with current thread pointer
3. Scheduler with priority support
4. Memory allocator (kalloc/kfree)
5. Interrupt disable/enable (pushcli/popcli)

### External References
1. NetBSD adaptive mutex
2. FreeBSD turnstile implementation
3. Linux futex design
4. Solaris priority inheritance

---

## Timeline

**Week 3:**
- Day 1: Data structures (Tasks 2.1.1-2.1.3)
- Day 2-3: Core operations (Tasks 2.2.1-2.2.5)
- Day 4: Turnstile (Tasks 2.3.1-2.3.4)
- Day 5: Priority inheritance (Tasks 2.4.1-2.4.2)

**Week 4:**
- Day 1-2: Testing (Tasks 2.5.1-2.5.3)
- Day 3: Documentation (Tasks 2.6.1-2.6.3)
- Day 4: Integration & bug fixes
- Day 5: Performance tuning & validation

---

## Success Metrics

- **Code:** ~1,500 lines of production code
- **Tests:** ~1,400 lines of test code
- **Docs:** ~1,100 lines of documentation
- **Commits:** ~10-12 commits
- **All tests:** PASSING ✅
- **Performance:** MEETS TARGETS ✅

---

**Status:** Ready to execute
**Next Action:** Begin Task 2.1.1 (Define adaptive_mutex structure)
