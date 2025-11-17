# ExoV6 Lock Implementation Roadmap - Option A
**Date:** 2025-11-17
**Status:** Active Development
**Target:** Complete novel lock subsystem for x86_64 QEMU

---

## Overview

This roadmap details the step-by-step implementation of ExoV6's novel lock subsystem, building on the design completed in LOCK_MODERNIZATION_DESIGN.md.

**Total Effort:** 12 weeks (6 phases × 2 weeks each)
**Current Phase:** Phase 1 (Week 1, Day 1)
**Completion:** 15% (design + skeleton)

---

## Phase 1: NUMA-Aware QSpinlock Foundation (Weeks 1-2)

### 1.1 Complete Core QSpinlock Implementation

**Goal:** Fully functional MCS-based queued spinlock

#### Step 1.1.1: Enhance NUMA Topology Detection
**File:** `kernel/sync/qspinlock.c`
**Estimated Time:** 4 hours

**Tasks:**
- [ ] Parse ACPI SRAT (System Resource Affinity Table)
  - Read ACPI tables from firmware
  - Extract proximity domain information
  - Map CPUs to NUMA nodes
- [ ] Fallback to CPUID-based detection
  - Use CPUID leaf 0x1F (Extended Topology)
  - Detect socket/core/thread topology
  - Infer NUMA from socket boundaries
- [ ] QEMU-specific detection
  - Parse `-numa` option hints
  - Detect via memory access latency probing
- [ ] Export `numa_node_count` and `cpu_to_numa[]` globally

**Dependencies:** None
**Output:** Accurate NUMA topology map

**Validation:**
```bash
# Test with QEMU multi-socket
qemu-system-x86_64 -smp 16,sockets=2,cores=4,threads=2 \
  -numa node,mem=2G,cpus=0-7 \
  -numa node,mem=2G,cpus=8-15
# Should detect 2 NUMA nodes
```

#### Step 1.1.2: Implement Hierarchical MCS Queue
**File:** `kernel/sync/qspinlock.c`
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Add local/remote queue separation to `struct mcs_node`
  ```c
  struct mcs_node {
      _Atomic(struct mcs_node *) next;
      _Atomic(struct mcs_node *) local_next;  // NEW: local socket waiters
      _Atomic uint32_t locked;
      uint32_t numa_node;
      uint8_t is_remote;  // NEW: flag for remote socket
  };
  ```
- [ ] Modify `qspin_lock()` to maintain two queues
  - Local queue: same NUMA node as lock holder
  - Remote queue: different NUMA nodes
- [ ] Modify `qspin_unlock()` to prefer local waiters
  - Check local_next first
  - If empty, check remote queue
  - 2:1 bias for local socket
- [ ] Handle queue transitions (local → remote)

**Dependencies:** Step 1.1.1
**Output:** NUMA-optimized lock handoff

**Validation:**
```c
// Test: Lock held by CPU 0 (node 0)
// Waiters: CPU 1 (node 0), CPU 8 (node 1)
// Expected: CPU 1 gets lock first (local preference)
```

#### Step 1.1.3: Add Performance Instrumentation
**File:** `kernel/sync/qspinlock.c`, `include/exo_lock.h`
**Estimated Time:** 3 hours

**Tasks:**
- [ ] Add per-lock statistics
  ```c
  struct qspin_stats {
      uint64_t fast_path_count;    // Uncontended acquisitions
      uint64_t slow_path_count;    // Queued acquisitions
      uint64_t local_handoff_count; // Local NUMA handoffs
      uint64_t remote_handoff_count;// Remote NUMA handoffs
      uint64_t total_spin_cycles;  // Total time spinning
      uint64_t max_queue_depth;    // Maximum waiters
  };
  ```
- [ ] Implement `qspin_dump_stats()`
- [ ] Add hooks for profiling tools
- [ ] Integrate with global `lock_stats`

**Dependencies:** Step 1.1.2
**Output:** Performance visibility

**Validation:**
```bash
# Run lock benchmark
./lockbench --mode=qspin --threads=8
# Check stats
cat /proc/lock_stats
```

#### Step 1.1.4: Optimize Fast Path
**File:** `kernel/sync/qspinlock.c`
**Estimated Time:** 4 hours

**Tasks:**
- [ ] Profile current fast path (measure cycle count)
- [ ] Inline `qspin_trylock_fast()` aggressively
- [ ] Use `likely()`/`unlikely()` branch hints
- [ ] Align hot code paths to cache line boundaries
- [ ] Minimize memory barriers in uncontended case
- [ ] Target < 10 cycles for fast path

**Dependencies:** Step 1.1.3 (need profiling)
**Output:** < 10 cycle fast path

**Validation:**
```c
// Microbenchmark
for (i = 0; i < 1000000; i++) {
    start = rdtsc();
    qspin_lock(&lock);
    qspin_unlock(&lock);
    end = rdtsc();
    avg_cycles += (end - start);
}
avg_cycles /= 1000000;
assert(avg_cycles < 10);
```

### 1.2 Integration and Testing

#### Step 1.2.1: Integrate with Build System
**File:** `kernel/sync/CMakeLists.txt`
**Estimated Time:** 2 hours

**Tasks:**
- [ ] Add `qspinlock.c` to kernel build
  ```cmake
  set(SYNC_SOURCES
      spinlock.c
      qspinlock.c  # NEW
      sleeplock.c
      rcu.c
  )
  ```
- [ ] Add feature flag `CONFIG_EXOLOCK_QSPIN`
- [ ] Conditional compilation support
- [ ] Test both legacy and new lock builds

**Dependencies:** Step 1.1.4
**Output:** Clean build with qspinlock

#### Step 1.2.2: Create Unit Tests
**File:** `tests/lock_tests.c` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Test 1: Basic acquire/release
- [ ] Test 2: Multi-threaded contention (2, 4, 8, 16 threads)
- [ ] Test 3: NUMA locality (verify local preference)
- [ ] Test 4: Nested locks (use all 4 MCS node slots)
- [ ] Test 5: Timeout detection
- [ ] Test 6: Statistics accuracy
- [ ] Test 7: Stress test (1M+ operations)

**Dependencies:** Step 1.2.1
**Output:** Passing test suite

**Validation:**
```bash
./test_qspinlock --all
# All tests PASS
```

#### Step 1.2.3: Create Microbenchmarks
**File:** `benchmarks/lockbench.c` (new)
**Estimated Time:** 4 hours

**Tasks:**
- [ ] Benchmark 1: Uncontended throughput
- [ ] Benchmark 2: 2-CPU ping-pong
- [ ] Benchmark 3: N-CPU contention (N=1,2,4,8,16)
- [ ] Benchmark 4: NUMA local vs remote
- [ ] Benchmark 5: Comparison vs ticket spinlock
- [ ] Generate CSV output for graphing

**Dependencies:** Step 1.2.2
**Output:** Performance baseline data

**Example Output:**
```
qspinlock_uncontended: 9.2 cycles/op
qspinlock_2cpu:        187 cycles/op
qspinlock_8cpu:        423 cycles/op (63% local, 37% remote)
ticket_spinlock_8cpu:  1842 cycles/op
Speedup: 4.35x
```

### Phase 1 Deliverables
- [x] Design document (completed)
- [x] Skeleton implementation (completed)
- [ ] Complete NUMA-aware qspinlock
- [ ] Integrated build
- [ ] Passing unit tests
- [ ] Benchmark results
- [ ] Phase 1 report document

**Estimated Completion:** End of Week 2

---

## Phase 2: Adaptive Mutex (Weeks 3-4)

### 2.1 Core Adaptive Mutex Implementation

**Goal:** illumos-style adaptive mutex with spin/block heuristics

#### Step 2.1.1: Implement Owner-Running Detection
**File:** `kernel/sync/adaptive_mutex.c` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Create `adaptive_mutex.c` and integrate with build
- [ ] Implement `is_owner_running()` heuristic
  ```c
  static inline int is_owner_running(struct proc *owner) {
      // Check if owner is currently scheduled on any CPU
      for (int i = 0; i < ncpu; i++) {
          if (cpus[i].proc == owner) {
              return 1;  // Owner is running
          }
      }
      return 0;  // Owner is blocked/sleeping
  }
  ```
- [ ] Add owner tracking to `struct adaptive_mutex`
  ```c
  struct adaptive_mutex {
      _Atomic uint64_t owner;  // PID or 0
      _Atomic uint32_t waiters;
      void *turnstile;
      uint32_t flags;
      struct adaptive_stats stats;
  };
  ```
- [ ] Implement basic acquire logic
  ```c
  void adaptive_lock(struct adaptive_mutex *lock) {
      if (tryacquire_fast(lock)) return;

      struct proc *owner = get_owner(lock);
      if (is_owner_running(owner)) {
          adaptive_spin(lock);  // Owner will release soon
      } else {
          adaptive_block(lock); // Owner won't run for a while
      }
  }
  ```

**Dependencies:** Phase 1 complete
**Output:** Basic adaptive behavior

#### Step 2.1.2: Implement Adaptive Spinning
**File:** `kernel/sync/adaptive_mutex.c`
**Estimated Time:** 5 hours

**Tasks:**
- [ ] Implement exponential backoff spinning
  ```c
  static void adaptive_spin(struct adaptive_mutex *lock) {
      int backoff = ADAPTIVE_SPIN_MIN_CYCLES;
      uint64_t start = rdtsc();

      while (is_locked(lock)) {
          struct proc *owner = get_owner(lock);

          // Re-evaluate: is owner still running?
          if (!is_owner_running(owner)) {
              adaptive_block(lock);  // Switch to blocking
              return;
          }

          // Spin with backoff
          for (int i = 0; i < backoff; i++) {
              pause();
          }

          if (backoff < ADAPTIVE_SPIN_MAX_CYCLES) {
              backoff *= 2;
          }

          // Timeout check
          if (rdtsc() - start > ADAPTIVE_SPIN_TIMEOUT) {
              adaptive_block(lock);  // Give up spinning
              return;
          }
      }

      // Lock became free during spin
      if (tryacquire(lock)) return;
      adaptive_block(lock);  // Race lost, block
  }
  ```
- [ ] Tune `ADAPTIVE_SPIN_MAX_CYCLES` empirically
- [ ] Add spin statistics (cycles, iterations)

**Dependencies:** Step 2.1.1
**Output:** Optimized spinning behavior

#### Step 2.1.3: Implement Turnstile Queue Infrastructure
**File:** `kernel/sync/turnstile.c` (new)
**Estimated Time:** 8 hours

**Tasks:**
- [ ] Design turnstile structure
  ```c
  struct turnstile {
      struct spinlock lock;        // Protects queue
      struct proc_list waiters;    // Priority-ordered waiters
      struct adaptive_mutex *owner;// Lock this is for
      uint32_t waiter_count;
  };
  ```
- [ ] Implement turnstile allocation
  ```c
  struct turnstile *turnstile_alloc(void);
  void turnstile_free(struct turnstile *ts);
  ```
- [ ] Implement priority-ordered insertion
  ```c
  void turnstile_insert(struct turnstile *ts, struct proc *p) {
      // Insert p into waiters sorted by priority
      // Higher priority processes go to front
  }
  ```
- [ ] Implement wakeup logic
  ```c
  void turnstile_wakeup(struct turnstile *ts) {
      // Wake highest priority waiter
      struct proc *p = turnstile_remove_highest(ts);
      wakeup(p);
  }
  ```
- [ ] Integrate with scheduler

**Dependencies:** Step 2.1.2
**Output:** Priority-aware blocking

#### Step 2.1.4: Implement Priority Inheritance
**File:** `kernel/sync/adaptive_mutex.c`, `kernel/sched/proc.c`
**Estimated Time:** 10 hours

**Tasks:**
- [ ] Add `inherited_priority` to `struct proc`
  ```c
  struct proc {
      // ... existing fields
      int base_priority;      // Original priority
      int inherited_priority; // Inherited from waiters
      int effective_priority; // max(base, inherited)
  };
  ```
- [ ] Implement priority inheritance on block
  ```c
  void adaptive_block(struct adaptive_mutex *lock) {
      struct proc *me = myproc();
      struct proc *owner = get_owner_proc(lock);

      // If my priority > owner's, boost owner
      if (me->effective_priority > owner->effective_priority) {
          owner->inherited_priority = me->effective_priority;
          sched_update_priority(owner);  // Reschedule if needed
      }

      // Add to turnstile and sleep
      turnstile_insert(lock->turnstile, me);
      sleep(lock->turnstile);
  }
  ```
- [ ] Implement priority de-inheritance on release
  ```c
  void adaptive_unlock(struct adaptive_mutex *lock) {
      struct proc *me = myproc();

      // Clear inherited priority
      me->inherited_priority = me->base_priority;
      sched_update_priority(me);

      // Wake next waiter
      if (lock->turnstile) {
          turnstile_wakeup(lock->turnstile);
      }

      release_lock(lock);
  }
  ```
- [ ] Update scheduler to use `effective_priority`
- [ ] Test priority inversion scenarios

**Dependencies:** Step 2.1.3
**Output:** No priority inversion

### 2.2 Optimization and Testing

#### Step 2.2.1: Optimize Fast Path (Assembly)
**File:** `kernel/sync/adaptive_mutex.S` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Implement assembly fast path for acquire
  ```asm
  # x86_64 adaptive_mutex_trylock_fast
  # Input: %rdi = lock pointer
  # Output: %rax = 1 (success), 0 (failure)

  .global adaptive_mutex_trylock_fast
  adaptive_mutex_trylock_fast:
      xorq %rax, %rax              # expected = 0 (free)
      movq %gs:current_pid, %rdx   # new owner = my PID
      lock cmpxchgq %rdx, (%rdi)   # Atomic CAS
      seteq %al                    # Set result
      ret
  ```
- [ ] Implement assembly fast path for release
- [ ] Measure cycle count (target < 10 cycles)
- [ ] Fall back to C for slow path

**Dependencies:** Step 2.1.4
**Output:** < 10 cycle fast path

#### Step 2.2.2: Tune Adaptive Heuristics
**File:** `kernel/sync/adaptive_mutex.c`
**Estimated Time:** 4 hours

**Tasks:**
- [ ] Run benchmarks with varying `ADAPTIVE_SPIN_MAX_CYCLES`
  - Test: 100, 500, 1000, 2000, 5000 cycles
  - Measure: context switches, throughput
- [ ] Run benchmarks with varying spin timeout
- [ ] Find optimal balance (minimize context switches without wasting CPU)
- [ ] Document tuning methodology

**Dependencies:** Step 2.2.1
**Output:** Optimal parameters

#### Step 2.2.3: Create Adaptive Mutex Tests
**File:** `tests/adaptive_mutex_tests.c` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Test 1: Basic acquire/release
- [ ] Test 2: Spin path (owner running)
- [ ] Test 3: Block path (owner blocked)
- [ ] Test 4: Priority inheritance
- [ ] Test 5: Priority inversion prevention
- [ ] Test 6: Turnstile ordering
- [ ] Test 7: Comparison vs spinlock (context switches)

**Dependencies:** Step 2.2.2
**Output:** Passing tests

### Phase 2 Deliverables
- [ ] Complete adaptive mutex implementation
- [ ] Turnstile queue infrastructure
- [ ] Priority inheritance
- [ ] Assembly-optimized fast path
- [ ] Passing unit tests
- [ ] Benchmark comparison (adaptive vs spinlock vs sleeplock)
- [ ] Phase 2 report

**Estimated Completion:** End of Week 4

---

## Phase 3: LWKT Tokens (Weeks 5-6)

### 3.1 Token Pool Infrastructure

**Goal:** DragonFlyBSD-style soft locks for capability traversal

#### Step 3.1.1: Implement Token Pool
**File:** `kernel/sync/lwkt_token.c` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Create token pool structure
  ```c
  #define TOKEN_POOL_SIZE 256
  struct lwkt_token token_pool[TOKEN_POOL_SIZE];
  ```
- [ ] Implement hash-based token allocation
  ```c
  uint32_t token_hash(const char *name) {
      // FNV-1a hash
      uint32_t hash = 2166136261u;
      for (const char *p = name; *p; p++) {
          hash ^= *p;
          hash *= 16777619u;
      }
      return hash % TOKEN_POOL_SIZE;
  }

  struct lwkt_token *token_get(const char *name) {
      uint32_t idx = token_hash(name);
      struct lwkt_token *token = &token_pool[idx];

      if (token->name == NULL) {
          token_init(token, name);
      }

      return token;
  }
  ```
- [ ] Handle hash collisions (chaining or open addressing)
- [ ] Implement token lifecycle management

**Dependencies:** Phase 2 complete
**Output:** Token pool ready

#### Step 3.1.2: Implement CPU Ownership Semantics
**File:** `kernel/sync/lwkt_token.c`
**Estimated Time:** 5 hours

**Tasks:**
- [ ] Modify `struct lwkt_token` for CPU ownership
  ```c
  struct lwkt_token {
      _Atomic uint32_t cpu_owner;  // CPU ID + 1 (0 = free)
      const char *name;
      uint64_t acquire_tsc;
      uint32_t depth;  // Nesting depth
  };
  ```
- [ ] Implement `token_acquire()`
  ```c
  void token_acquire(struct lwkt_token *token) {
      struct cpu *c = mycpu();
      uint32_t my_cpu_id = c - cpus + 1;  // 1-indexed

      // Spin until we get it
      while (1) {
          uint32_t owner = atomic_load(&token->cpu_owner);

          if (owner == 0) {
              // Free - try to acquire
              uint32_t expected = 0;
              if (atomic_compare_exchange_strong(&token->cpu_owner,
                                                &expected, my_cpu_id)) {
                  token->acquire_tsc = rdtsc();
                  token->depth++;
                  return;  // Got it
              }
          } else if (owner == my_cpu_id) {
              // Already own it - nested acquisition
              token->depth++;
              return;
          } else {
              // Another CPU owns it - spin
              pause();
          }
      }
  }
  ```
- [ ] Implement `token_release()`
  ```c
  void token_release(struct lwkt_token *token) {
      struct cpu *c = mycpu();
      uint32_t my_cpu_id = c - cpus + 1;

      if (atomic_load(&token->cpu_owner) != my_cpu_id) {
          panic("token_release: not owner");
      }

      if (--token->depth == 0) {
          atomic_store(&token->cpu_owner, 0);  // Release
      }
  }
  ```

**Dependencies:** Step 3.1.1
**Output:** CPU-owned tokens

#### Step 3.1.3: Implement Automatic Release on Block
**File:** `kernel/sync/lwkt_token.c`, `kernel/sched/proc.c`
**Estimated Time:** 8 hours

**Tasks:**
- [ ] Track held tokens per-CPU
  ```c
  struct cpu {
      // ... existing fields
      struct lwkt_token *held_tokens[MAX_TOKENS_PER_CPU];
      int held_token_count;
  };
  ```
- [ ] Implement `token_release_all()`
  ```c
  void token_release_all(void) {
      struct cpu *c = mycpu();

      for (int i = 0; i < c->held_token_count; i++) {
          struct lwkt_token *token = c->held_tokens[i];
          token->depth = 0;  // Force release
          atomic_store(&token->cpu_owner, 0);
      }

      c->held_token_count = 0;
  }
  ```
- [ ] Hook into scheduler's `sched()` function
  ```c
  void sched(void) {
      // ... existing code

      // Release all tokens before context switch
      token_release_all();

      swtch(&p->context, mycpu()->scheduler);

      // Reacquire tokens after resume
      token_reacquire_all();
  }
  ```
- [ ] Implement `token_reacquire_all()`
  ```c
  void token_reacquire_all(void) {
      struct cpu *c = mycpu();

      for (int i = 0; i < c->held_token_count; i++) {
          token_acquire(c->held_tokens[i]);
      }
  }
  ```
- [ ] Test with blocking syscalls

**Dependencies:** Step 3.1.2
**Output:** Automatic token management

### 3.2 Capability System Integration

#### Step 3.2.1: Integrate Tokens with Capabilities
**File:** `kernel/cap.c`, `kernel/sync/lwkt_token.c`
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Add token field to capability structures
  ```c
  struct cap_entry {
      // ... existing fields
      struct lwkt_token *lock_token;  // NEW
  };
  ```
- [ ] Modify capability operations to use tokens
  ```c
  int cap_validate_with_token(cap_id_t id, struct cap_entry *out) {
      struct lwkt_token *token = token_get("cap_table");
      token_acquire(token);

      int result = cap_validate_internal(id, out);

      token_release(token);
      return result;
  }
  ```
- [ ] Handle token release on capability blocking (e.g., IPC)
  ```c
  int exo_send(exo_cap dest, const void *buf, uint64_t len) {
      // Validate capability (acquires token)
      struct cap_entry entry;
      if (cap_validate_with_token(dest, &entry) != 0) {
          return -1;
      }

      // About to block on send - tokens will auto-release
      // via sched() hook
      return send_message_blocking(&entry, buf, len);
  }
  ```
- [ ] Test capability traversal with automatic token release

**Dependencies:** Step 3.1.3
**Output:** Capability-aware tokens

#### Step 3.2.2: Add TSC-Based Windowing
**File:** `kernel/sync/lwkt_token.c`
**Estimated Time:** 4 hours

**Tasks:**
- [ ] Implement contention detection via TSC
  ```c
  #define TOKEN_CONTENTION_WINDOW (10000000ULL)  // 10ms @ 1GHz

  void token_acquire(struct lwkt_token *token) {
      uint64_t start_tsc = rdtsc();

      while (...) {
          // ... acquisition logic

          uint64_t elapsed = rdtsc() - start_tsc;
          if (elapsed > TOKEN_CONTENTION_WINDOW) {
              // High contention detected
              token_stats.contention_events++;

              // Adaptive backoff or yield
              if (elapsed > TOKEN_CONTENTION_WINDOW * 10) {
                  yield();  // Give up CPU
              }
          }
      }
  }
  ```
- [ ] Add contention statistics
- [ ] Tune window size empirically

**Dependencies:** Step 3.2.1
**Output:** Contention-aware tokens

### 3.3 Testing

#### Step 3.3.1: Create Token Tests
**File:** `tests/lwkt_token_tests.c` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Test 1: Basic acquire/release
- [ ] Test 2: Nested acquisition (same token)
- [ ] Test 3: Multiple tokens
- [ ] Test 4: Automatic release on block
- [ ] Test 5: Reacquisition after resume
- [ ] Test 6: Hash collision handling
- [ ] Test 7: Capability integration

**Dependencies:** Step 3.2.2
**Output:** Passing tests

### Phase 3 Deliverables
- [ ] Complete LWKT token implementation
- [ ] Token pool with hash distribution
- [ ] Automatic release/reacquire
- [ ] Capability system integration
- [ ] TSC-based contention handling
- [ ] Passing unit tests
- [ ] Phase 3 report

**Estimated Completion:** End of Week 6

---

## Phase 4: DAG Lock Verification (Weeks 7-8)

### 4.1 Lock Ordering Graph

**Goal:** Deadlock-free guarantees via DAG enforcement

#### Step 4.1.1: Build Lock Ordering Graph
**File:** `kernel/sync/dag_lock.c` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Create global lock graph
  ```c
  struct lock_graph {
      struct spinlock lock;
      struct lock_dag_node *nodes[MAX_LOCKS];
      int node_count;
      uint64_t adjacency[MAX_LOCKS];  // Bitmap of dependencies
  };

  struct lock_graph global_lock_graph;
  ```
- [ ] Implement `dag_register_lock()`
  ```c
  int dag_register_lock(struct exo_lock *lock, uint32_t level) {
      acquire(&global_lock_graph.lock);

      struct lock_dag_node *node = &lock->dag;
      node->level = level;
      node->dependency_bitmap = 0;

      global_lock_graph.nodes[global_lock_graph.node_count++] = node;

      release(&global_lock_graph.lock);
      return 0;
  }
  ```
- [ ] Implement `dag_add_dependency()`
  ```c
  void dag_add_dependency(struct exo_lock *lock, struct exo_lock *depends_on) {
      // lock must be acquired after depends_on
      lock->dag.dependency_bitmap |= (1ULL << depends_on->dag.node_id);
  }
  ```

**Dependencies:** Phase 3 complete
**Output:** Lock graph infrastructure

#### Step 4.1.2: Implement Runtime Verification
**File:** `kernel/sync/dag_lock.c`
**Estimated Time:** 8 hours

**Tasks:**
- [ ] Track held locks per-process
  ```c
  struct proc {
      // ... existing fields
      struct exo_lock *held_locks[MAX_HELD_LOCKS];
      int held_lock_count;
  };
  ```
- [ ] Implement `dag_verify_order()`
  ```c
  int dag_verify_order(struct exo_lock *new_lock) {
      struct proc *p = myproc();

      // Check if acquiring new_lock would violate ordering
      for (int i = 0; i < p->held_lock_count; i++) {
          struct exo_lock *held = p->held_locks[i];

          // Rule: held lock level must be < new lock level
          if (held->dag.level >= new_lock->dag.level) {
              cprintf("DAG violation: acquiring %s (level %d) while holding %s (level %d)\n",
                      new_lock->name, new_lock->dag.level,
                      held->name, held->dag.level);
              return -1;  // Violation
          }
      }

      return 0;  // OK
  }
  ```
- [ ] Integrate into `exo_lock_acquire()`
  ```c
  void exo_lock_acquire(struct exo_lock *lock) {
      if (dag_verify_order(lock) != 0) {
          panic("DAG lock ordering violation");
      }

      // Proceed with acquisition
      switch (lock->type) {
          case EXOLOCK_QSPIN:
              qspin_lock(&lock->qspin);
              break;
          // ... other types
      }

      // Track held lock
      struct proc *p = myproc();
      p->held_locks[p->held_lock_count++] = lock;
  }
  ```
- [ ] Implement cycle detection (optional, for debugging)
  ```c
  int dag_detect_cycle(struct lock_dag_node *start) {
      // DFS to detect cycles
      // Returns 1 if cycle found, 0 otherwise
  }
  ```

**Dependencies:** Step 4.1.1
**Output:** Runtime deadlock prevention

### 4.2 Capability Level Mapping

#### Step 4.2.1: Map Capabilities to DAG Levels
**File:** `kernel/cap.c`, `kernel/sync/dag_lock.c`
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Define capability level hierarchy
  ```c
  enum cap_dag_level {
      CAP_LEVEL_PROCESS = 0,   // Process capabilities
      CAP_LEVEL_MEMORY  = 1,   // Memory/page capabilities
      CAP_LEVEL_IO      = 2,   // I/O port, block device capabilities
      CAP_LEVEL_IRQ     = 3,   // Interrupt capabilities
      CAP_LEVEL_MAX     = 4
  };
  ```
- [ ] Assign levels to capability types
  ```c
  static uint32_t cap_type_to_dag_level(cap_type_t type) {
      switch (type) {
          case CAP_TYPE_PROCESS:
          case CAP_TYPE_ENDPOINT:
              return CAP_LEVEL_PROCESS;

          case CAP_TYPE_PAGE:
          case CAP_TYPE_MEMORY:
              return CAP_LEVEL_MEMORY;

          case CAP_TYPE_BLOCK:
          case CAP_TYPE_IOPORT:
              return CAP_LEVEL_IO;

          case CAP_TYPE_IRQ:
              return CAP_LEVEL_IRQ;

          default:
              return CAP_LEVEL_MAX;
      }
  }
  ```
- [ ] Initialize capability locks with correct levels
  ```c
  void cap_table_init(void) {
      exo_lock_init(&cap_table_lock, EXOLOCK_TOKEN, "cap_table",
                    CAP_LEVEL_PROCESS);

      for (int i = 0; i < CAP_TABLE_SIZE; i++) {
          struct cap_entry *entry = &cap_table[i];
          if (entry->type != CAP_TYPE_NONE) {
              uint32_t level = cap_type_to_dag_level(entry->type);
              exo_lock_init(&entry->lock, EXOLOCK_ADAPTIVE,
                           entry->name, level);
          }
      }
  }
  ```
- [ ] Document capability lock ordering rules

**Dependencies:** Step 4.1.2
**Output:** Capability DAG hierarchy

### 4.3 Violation Logging and Diagnostics

#### Step 4.3.1: Implement Violation Logging
**File:** `kernel/sync/dag_lock.c`
**Estimated Time:** 4 hours

**Tasks:**
- [ ] Create violation log buffer
  ```c
  struct dag_violation {
      uint64_t timestamp;
      char new_lock_name[32];
      uint32_t new_lock_level;
      char held_lock_name[32];
      uint32_t held_lock_level;
      uint32_t pid;
      uint64_t rip;  // Instruction pointer
  };

  #define DAG_VIOLATION_LOG_SIZE 1024
  struct dag_violation violation_log[DAG_VIOLATION_LOG_SIZE];
  int violation_log_idx = 0;
  ```
- [ ] Log violations in `dag_verify_order()`
  ```c
  void dag_log_violation(struct exo_lock *new_lock, struct exo_lock *held) {
      struct dag_violation *v = &violation_log[violation_log_idx++];
      violation_log_idx %= DAG_VIOLATION_LOG_SIZE;

      v->timestamp = rdtsc();
      strncpy(v->new_lock_name, new_lock->name, 31);
      v->new_lock_level = new_lock->dag.level;
      strncpy(v->held_lock_name, held->name, 31);
      v->held_lock_level = held->dag.level;
      v->pid = myproc()->pid;
      v->rip = read_rip();
  }
  ```
- [ ] Expose via `/proc/dag_violations`
- [ ] Add violation statistics

**Dependencies:** Step 4.2.1
**Output:** Violation diagnostics

### 4.4 Testing

#### Step 4.4.1: Create DAG Tests
**File:** `tests/dag_lock_tests.c` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Test 1: Correct ordering (no violations)
- [ ] Test 2: Reverse ordering (detect violation)
- [ ] Test 3: Multi-level hierarchy
- [ ] Test 4: Capability lock ordering
- [ ] Test 5: Cycle detection
- [ ] Test 6: Violation logging
- [ ] Test 7: Performance overhead measurement

**Dependencies:** Step 4.3.1
**Output:** Passing tests

### Phase 4 Deliverables
- [ ] Complete DAG verification system
- [ ] Lock ordering graph
- [ ] Runtime violation detection
- [ ] Capability level mapping
- [ ] Violation logging
- [ ] Passing unit tests
- [ ] Phase 4 report

**Estimated Completion:** End of Week 8

---

## Phase 5: Resurrection Server (Weeks 9-10)

### 5.1 Lock Monitoring Infrastructure

**Goal:** Self-healing via automatic deadlock detection and recovery

#### Step 5.1.1: Create Monitoring Thread
**File:** `kernel/sync/resurrection_server.c` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Create resurrection server thread
  ```c
  void resurrection_server_main(void) {
      while (1) {
          lock_health_check();
          sleep_ms(1);  // 1ms tick
      }
  }

  void resurrection_server_start(void) {
      struct proc *p = proc_alloc();
      p->name = "resurrection_server";
      p->state = RUNNABLE;
      p->entry = resurrection_server_main;
      // High priority - must run frequently
      p->priority = PRIORITY_MAX;
  }
  ```
- [ ] Implement lock registration
  ```c
  void lock_register_monitor(struct exo_lock *lock) {
      acquire(&monitor_lock);
      monitored_locks[monitored_lock_count++] = lock;
      release(&monitor_lock);
  }
  ```
- [ ] Create monitored lock array
  ```c
  #define MAX_MONITORED_LOCKS 4096
  struct exo_lock *monitored_locks[MAX_MONITORED_LOCKS];
  int monitored_lock_count = 0;
  ```

**Dependencies:** Phase 4 complete
**Output:** Monitoring infrastructure

#### Step 5.1.2: Implement Health Checks
**File:** `kernel/sync/resurrection_server.c`
**Estimated Time:** 8 hours

**Tasks:**
- [ ] Implement `lock_health_check()`
  ```c
  void lock_health_check(void) {
      uint64_t now = rdtsc();

      for (int i = 0; i < monitored_lock_count; i++) {
          struct exo_lock *lock = monitored_locks[i];

          // Check if lock is held
          if (!exo_lock_is_held(lock)) {
              continue;  // Free, no issue
          }

          // Get holder and hold time
          struct proc *holder = exo_lock_get_holder(lock);
          uint64_t hold_time = now - lock->acquire_tsc;

          // Check for timeout
          if (hold_time > LOCK_TIMEOUT_CYCLES) {
              // Potential issue
              lock_handle_timeout(lock, holder, hold_time);
          }

          // Check waiter count
          uint32_t waiters = exo_lock_get_waiter_count(lock);
          if (waiters > 0 && hold_time > LOCK_TIMEOUT_CYCLES / 2) {
              // Lock held with waiters - potential contention
              lock->stats.contention_count++;
          }
      }
  }
  ```
- [ ] Implement helper functions
  ```c
  int exo_lock_is_held(struct exo_lock *lock);
  struct proc *exo_lock_get_holder(struct exo_lock *lock);
  uint32_t exo_lock_get_waiter_count(struct exo_lock *lock);
  ```
- [ ] Add `acquire_tsc` tracking to lock structures

**Dependencies:** Step 5.1.1
**Output:** Automatic health monitoring

### 5.2 Recovery Mechanisms

#### Step 5.2.1: Implement Force Release
**File:** `kernel/sync/resurrection_server.c`
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Implement `lock_force_release()`
  ```c
  int lock_force_release(struct exo_lock *lock) {
      struct proc *holder = exo_lock_get_holder(lock);

      cprintf("RESURRECTION: Force-releasing lock %s (holder PID %d)\n",
              lock->name, holder->pid);

      // Clear lock state forcibly
      switch (lock->type) {
          case EXOLOCK_QSPIN:
              atomic_store(&lock->qspin.val, 0);
              break;

          case EXOLOCK_ADAPTIVE:
              atomic_store(&lock->adaptive.owner, 0);
              // Wake all waiters
              if (lock->adaptive.turnstile) {
                  turnstile_wakeup_all(lock->adaptive.turnstile);
              }
              break;

          case EXOLOCK_TOKEN:
              atomic_store(&lock->token.cpu_owner, 0);
              lock->token.depth = 0;
              break;

          case EXOLOCK_SLEEP:
              atomic_store(&lock->sleep.locked, 0);
              atomic_store(&lock->sleep.holder_pid, 0);
              wakeup(lock->sleep.wait_queue);
              break;
      }

      // Remove from holder's held_locks
      if (holder) {
          proc_remove_held_lock(holder, lock);
      }

      return 0;
  }
  ```
- [ ] Add safety checks (prevent force-release of critical locks)
- [ ] Log force-release events

**Dependencies:** Step 5.1.2
**Output:** Force-release capability

#### Step 5.2.2: Implement Process Kill and Restart
**File:** `kernel/sync/resurrection_server.c`, `kernel/sched/proc.c`
**Estimated Time:** 8 hours

**Tasks:**
- [ ] Implement `lock_handle_timeout()`
  ```c
  void lock_handle_timeout(struct exo_lock *lock, struct proc *holder,
                          uint64_t hold_time) {
      // Check if holder is still alive
      if (!proc_is_alive(holder->pid)) {
          // Dead lock holder
          cprintf("RESURRECTION: Dead holder detected (PID %d, lock %s)\n",
                  holder->pid, lock->name);

          lock_force_release(lock);
          resurrection_event_log(LOCK_RESURRECTION_FORCE_RELEASE,
                                holder->pid, lock);
          return;
      }

      // Holder alive but stuck
      if (hold_time > LOCK_CRITICAL_TIMEOUT) {
          cprintf("RESURRECTION: Killing stuck process (PID %d, lock %s, hold_time %llu)\n",
                  holder->pid, lock->name, hold_time);

          // Kill the process
          kill(holder->pid);

          // Force-release the lock
          lock_force_release(lock);

          // Restart the process (if restartable)
          if (proc_is_restartable(holder)) {
              struct proc *new_proc = proc_restart(holder);
              cprintf("RESURRECTION: Restarted as PID %d\n", new_proc->pid);
          }

          resurrection_event_log(LOCK_TIMEOUT_KILL, holder->pid, lock);
      }
  }
  ```
- [ ] Implement `proc_is_restartable()`
  - Check if process has restart metadata
  - LibOS services should be restartable
  - User processes may not be
- [ ] Implement `proc_restart()`
  ```c
  struct proc *proc_restart(struct proc *old) {
      // Allocate new process
      struct proc *new = proc_alloc();

      // Copy restart metadata
      new->name = old->name;
      new->entry = old->entry;
      new->pgdir = setupkvm();  // Fresh page table

      // Initialize state
      new->state = RUNNABLE;
      new->priority = old->priority;

      // Clean up old process
      proc_cleanup(old);

      return new;
  }
  ```
- [ ] Test kill and restart scenarios

**Dependencies:** Step 5.2.1
**Output:** Automatic recovery

### 5.3 Event Logging

#### Step 5.3.1: Implement Event Log
**File:** `kernel/sync/resurrection_server.c`
**Estimated Time:** 4 hours

**Tasks:**
- [ ] Create event log structure
  ```c
  struct resurrection_event {
      uint64_t timestamp;
      resurrection_event_t type;
      uint32_t pid;
      char lock_name[32];
      uint64_t hold_time;
      char details[128];
  };

  #define RESURRECTION_LOG_SIZE 4096
  struct resurrection_event resurrection_log[RESURRECTION_LOG_SIZE];
  int resurrection_log_idx = 0;
  ```
- [ ] Implement `resurrection_event_log()`
  ```c
  void resurrection_event_log(resurrection_event_t event, uint32_t pid,
                             struct exo_lock *lock) {
      struct resurrection_event *e = &resurrection_log[resurrection_log_idx++];
      resurrection_log_idx %= RESURRECTION_LOG_SIZE;

      e->timestamp = rdtsc();
      e->type = event;
      e->pid = pid;
      strncpy(e->lock_name, lock->name, 31);
      e->hold_time = rdtsc() - lock->acquire_tsc;

      // Event-specific details
      switch (event) {
          case LOCK_RESURRECTION_FORCE_RELEASE:
              snprintf(e->details, 127, "Dead holder detected");
              break;
          case LOCK_TIMEOUT_KILL:
              snprintf(e->details, 127, "Process killed and restarted");
              break;
          case LOCK_DEADLOCK_DETECTED:
              snprintf(e->details, 127, "Deadlock cycle detected");
              break;
      }
  }
  ```
- [ ] Expose via `/proc/resurrection_log`
- [ ] Add statistics (total events, by type)

**Dependencies:** Step 5.2.2
**Output:** Event logging

### 5.4 Testing

#### Step 5.4.1: Create Resurrection Tests
**File:** `tests/resurrection_tests.c` (new)
**Estimated Time:** 8 hours

**Tasks:**
- [ ] Test 1: Dead lock holder detection
  ```c
  // Acquire lock, kill holder, verify force-release
  ```
- [ ] Test 2: Stuck process detection
  ```c
  // Acquire lock, spin forever, verify kill & restart
  ```
- [ ] Test 3: Timeout thresholds
  ```c
  // Verify LOCK_TIMEOUT_CYCLES and LOCK_CRITICAL_TIMEOUT
  ```
- [ ] Test 4: Restartable vs non-restartable processes
- [ ] Test 5: Event logging accuracy
- [ ] Test 6: False positive avoidance
  ```c
  // Long-held lock that's legitimate (e.g., I/O)
  ```
- [ ] Test 7: Performance overhead (should be < 1%)

**Dependencies:** Step 5.3.1
**Output:** Passing tests

### Phase 5 Deliverables
- [ ] Complete resurrection server
- [ ] Lock monitoring thread (1ms tick)
- [ ] Health checks via TSC
- [ ] Force-release mechanism
- [ ] Process kill and restart
- [ ] Event logging
- [ ] Passing unit tests
- [ ] Phase 5 report

**Estimated Completion:** End of Week 10

---

## Phase 6: Physics-Inspired Optimization (Weeks 11-12)

### 6.1 Simulated Annealing Optimizer

**Goal:** Optimize lock memory layout to minimize cache contention

#### Step 6.1.1: Implement Annealing Engine
**File:** `kernel/sync/lock_optimizer.c` (new)
**Estimated Time:** 8 hours

**Tasks:**
- [ ] Implement `lock_optimize_layout()`
  ```c
  void lock_optimize_layout(struct exo_lock *locks[], size_t count,
                           uint32_t iterations) {
      double temperature = ANNEAL_INITIAL_TEMP;
      const double cooling_rate = ANNEAL_COOLING_RATE;

      while (temperature > ANNEAL_MIN_TEMP) {
          for (uint32_t iter = 0; iter < iterations; iter++) {
              // Random swap
              int i = random() % count;
              int j = random() % count;

              // Calculate energy before swap
              double old_energy = calculate_contention_energy(locks, count);

              // Perform swap
              swap_lock_positions(&locks[i], &locks[j]);

              // Calculate energy after swap
              double new_energy = calculate_contention_energy(locks, count);

              // Metropolis criterion
              double delta_E = new_energy - old_energy;
              if (delta_E < 0 || random_double() < exp(-delta_E / temperature)) {
                  // Accept new configuration
              } else {
                  // Revert swap
                  swap_lock_positions(&locks[j], &locks[i]);
              }
          }

          temperature *= cooling_rate;
      }
  }
  ```
- [ ] Implement `calculate_contention_energy()`
  ```c
  double calculate_contention_energy(struct exo_lock *locks[], size_t count) {
      double energy = 0.0;

      for (size_t i = 0; i < count; i++) {
          for (size_t j = i+1; j < count; j++) {
              // Check if locks share cache line
              if (same_cache_line(&locks[i], &locks[j])) {
                  // Penalty = product of access frequencies
                  double freq_i = locks[i]->stats.acquire_count;
                  double freq_j = locks[j]->stats.acquire_count;
                  energy += freq_i * freq_j;
              }
          }
      }

      return energy;
  }
  ```
- [ ] Implement `swap_lock_positions()`
  - Physically move locks in memory
  - Update all references
- [ ] Implement random number generator

**Dependencies:** Phase 5 complete
**Output:** Layout optimizer

#### Step 6.1.2: Add Access Pattern Profiling
**File:** `kernel/sync/lock_optimizer.c`
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Track access patterns per lock
  ```c
  struct lock_access_pattern {
      uint64_t access_times[PROFILE_WINDOW];  // Circular buffer
      int access_idx;
      double access_frequency;  // Accesses per second
  };
  ```
- [ ] Record accesses in `exo_lock_acquire()`
  ```c
  void exo_lock_acquire(struct exo_lock *lock) {
      // ... existing code

      // Profile access
      lock->pattern.access_times[lock->pattern.access_idx++] = rdtsc();
      lock->pattern.access_idx %= PROFILE_WINDOW;
  }
  ```
- [ ] Calculate access frequency
  ```c
  void update_access_frequency(struct exo_lock *lock) {
      uint64_t now = rdtsc();
      uint64_t window_start = lock->pattern.access_times[0];
      uint64_t elapsed = now - window_start;

      int access_count = PROFILE_WINDOW;
      double seconds = (double)elapsed / tsc_frequency;

      lock->pattern.access_frequency = access_count / seconds;
  }
  ```
- [ ] Run profiling periodically (e.g., every 10 seconds)

**Dependencies:** Step 6.1.1
**Output:** Access frequency data

### 6.2 Entangled Lock Pairs

**Goal:** Atomic dual acquisition for correlated locks

#### Step 6.2.1: Implement Correlation Detection
**File:** `kernel/sync/lock_optimizer.c`
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Track lock pair accesses
  ```c
  struct lock_pair_access {
      struct exo_lock *lock_a;
      struct exo_lock *lock_b;
      uint64_t joint_accesses;    // Both acquired together
      uint64_t separate_accesses; // Acquired separately
      double correlation;         // joint / (joint + separate)
  };
  ```
- [ ] Detect joint acquisitions
  ```c
  void track_lock_pair(struct exo_lock *a, struct exo_lock *b) {
      struct proc *p = myproc();

      // Check if both are in held_locks
      int has_a = 0, has_b = 0;
      for (int i = 0; i < p->held_lock_count; i++) {
          if (p->held_locks[i] == a) has_a = 1;
          if (p->held_locks[i] == b) has_b = 1;
      }

      if (has_a && has_b) {
          // Joint acquisition
          struct lock_pair_access *pair = find_or_create_pair(a, b);
          pair->joint_accesses++;
      }
  }
  ```
- [ ] Calculate correlation
  ```c
  void update_correlation(struct lock_pair_access *pair) {
      uint64_t total = pair->joint_accesses + pair->separate_accesses;
      if (total > 0) {
          pair->correlation = (double)pair->joint_accesses / total;
      }
  }
  ```
- [ ] Identify highly correlated pairs (> 0.8)

**Dependencies:** Step 6.1.2
**Output:** Correlated lock pairs

#### Step 6.2.2: Implement Entangled Acquisition
**File:** `kernel/sync/entangled_lock.c` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Implement `entangled_pair_init()`
  ```c
  void entangled_pair_init(struct entangled_lock_pair *pair,
                          struct exo_lock *a, struct exo_lock *b) {
      pair->lock_a = a;
      pair->lock_b = b;
      pair->correlation = 0.0;
      atomic_store(&pair->joint_state, 0);
  }
  ```
- [ ] Implement `entangled_pair_acquire()`
  ```c
  void entangled_pair_acquire(struct entangled_lock_pair *pair) {
      if (pair->correlation > ENTANGLE_CORRELATION_MIN) {
          // High correlation: try atomic dual acquisition
          uint64_t expected = 0;  // Both free
          uint64_t desired = encode_dual_owner(mycpu());

          if (atomic_compare_exchange_strong(&pair->joint_state,
                                            &expected, desired)) {
              // Got both atomically!
              return;
          }
      }

      // Fallback: acquire separately
      exo_lock_acquire(pair->lock_a);
      exo_lock_acquire(pair->lock_b);
  }
  ```
- [ ] Implement `entangled_pair_release()`
  ```c
  void entangled_pair_release(struct entangled_lock_pair *pair) {
      if (pair->correlation > ENTANGLE_CORRELATION_MIN) {
          // Atomic dual release
          atomic_store(&pair->joint_state, 0);
      } else {
          // Release separately
          exo_lock_release(pair->lock_b);
          exo_lock_release(pair->lock_a);
      }
  }
  ```
- [ ] Test with common lock pairs (e.g., proc.lock + proc.mem_lock)

**Dependencies:** Step 6.2.1
**Output:** Entangled acquisition

### 6.3 Runtime Adaptation

#### Step 6.3.1: Implement Continuous Optimization
**File:** `kernel/sync/lock_optimizer.c`
**Estimated Time:** 4 hours

**Tasks:**
- [ ] Create background optimizer thread
  ```c
  void lock_optimizer_main(void) {
      while (1) {
          // Update access frequencies
          for (int i = 0; i < lock_count; i++) {
              update_access_frequency(&locks[i]);
          }

          // Update correlations
          for (int i = 0; i < pair_count; i++) {
              update_correlation(&lock_pairs[i]);
          }

          // Re-optimize layout periodically
          static int cycle = 0;
          if (++cycle % 100 == 0) {  // Every 100 seconds
              lock_optimize_layout(locks, lock_count, 1000);
          }

          sleep_seconds(1);
      }
  }
  ```
- [ ] Start optimizer thread at boot
- [ ] Make optimization parameters tunable

**Dependencies:** Step 6.2.2
**Output:** Continuous adaptation

### 6.4 Testing and Benchmarking

#### Step 6.4.1: Create Optimization Tests
**File:** `tests/lock_optimizer_tests.c` (new)
**Estimated Time:** 6 hours

**Tasks:**
- [ ] Test 1: Simulated annealing convergence
- [ ] Test 2: Access pattern profiling accuracy
- [ ] Test 3: Correlation detection
- [ ] Test 4: Entangled pair acquisition
- [ ] Test 5: Layout optimization effectiveness
- [ ] Test 6: Continuous adaptation
- [ ] Test 7: Performance improvement measurement

**Dependencies:** Step 6.3.1
**Output:** Passing tests

#### Step 6.4.2: Run Final Benchmarks
**File:** `benchmarks/final_lockbench.c` (new)
**Estimated Time:** 4 hours

**Tasks:**
- [ ] Benchmark all lock types
  - qspinlock
  - adaptive_mutex
  - lwkt_token
  - sleeplock
  - Legacy spinlock (for comparison)
- [ ] Benchmark with optimization ON vs OFF
- [ ] Measure:
  - Throughput (ops/sec)
  - Latency (cycles/op)
  - Cache misses
  - Context switches
  - NUMA locality
- [ ] Generate comparison graphs
- [ ] Document performance improvements

**Dependencies:** Step 6.4.1
**Output:** Final benchmark results

### Phase 6 Deliverables
- [ ] Complete physics-inspired optimization
- [ ] Simulated annealing layout optimizer
- [ ] Access pattern profiling
- [ ] Entangled lock pair detection and acquisition
- [ ] Continuous runtime adaptation
- [ ] Passing unit tests
- [ ] Final benchmark results
- [ ] Phase 6 report

**Estimated Completion:** End of Week 12

---

## Final Integration and Documentation

### Post-Phase 6: Final Steps

#### Integration Testing (Week 13)
**Estimated Time:** 20 hours

- [ ] Full system integration test
- [ ] Stress testing with real workloads
- [ ] QEMU boot with all locks enabled
- [ ] Multi-socket NUMA testing
- [ ] Deadlock injection tests
- [ ] Resurrection server live testing
- [ ] Performance regression testing

#### Documentation (Week 13)
**Estimated Time:** 16 hours

- [ ] API documentation (Doxygen)
- [ ] Architecture overview
- [ ] User guide for lock selection
- [ ] Performance tuning guide
- [ ] Troubleshooting guide
- [ ] Update MODERNIZATION_ROADMAP.md with results
- [ ] Write academic paper draft (optional)

#### Final Commit and Review (Week 13)
**Estimated Time:** 4 hours

- [ ] Create comprehensive commit message
- [ ] Push to branch
- [ ] Create pull request
- [ ] Code review (self-review or with team)
- [ ] Address review comments
- [ ] Merge to main branch

---

## Success Criteria

### Phase 1 Success Criteria
- [x] qspinlock compiles without errors
- [ ] NUMA topology detection works in QEMU
- [ ] Hierarchical queuing functional
- [ ] Fast path < 10 cycles
- [ ] All unit tests pass
- [ ] Benchmarks show improvement over ticket spinlock

### Phase 2 Success Criteria
- [ ] Adaptive mutex compiles without errors
- [ ] Spin/block heuristic working correctly
- [ ] Turnstile queues functional
- [ ] Priority inheritance prevents inversion
- [ ] Fast path < 10 cycles
- [ ] Context switches reduced vs sleeplock

### Phase 3 Success Criteria
- [ ] LWKT tokens compile without errors
- [ ] Automatic release on block works
- [ ] Capability integration functional
- [ ] No false releases
- [ ] Token contention handled gracefully

### Phase 4 Success Criteria
- [ ] DAG verification compiles without errors
- [ ] Lock ordering violations detected
- [ ] Capability hierarchy enforced
- [ ] No false positives
- [ ] Performance overhead < 5%

### Phase 5 Success Criteria
- [ ] Resurrection server compiles without errors
- [ ] Dead lock holders detected and released
- [ ] Stuck processes killed and restarted
- [ ] Event logging accurate
- [ ] Performance overhead < 1%
- [ ] No false positives

### Phase 6 Success Criteria
- [ ] Optimizer compiles without errors
- [ ] Simulated annealing converges
- [ ] Access profiling accurate
- [ ] Entangled pairs detected
- [ ] Cache misses reduced
- [ ] Performance improvement > 2x on contended workloads

### Overall Success Criteria
- [ ] Zero compilation errors
- [ ] All unit tests pass (> 50 tests)
- [ ] All benchmarks show improvement
- [ ] QEMU boots successfully with all locks
- [ ] No deadlocks in stress testing
- [ ] Resurrection server recovers from injected faults
- [ ] Performance targets met (see Phase 1 targets)
- [ ] Documentation complete

---

## Risk Management

### Identified Risks

1. **ACPI SRAT parsing complexity**
   - **Mitigation:** Fallback to CPUID-based detection
   - **Contingency:** Manual NUMA configuration

2. **Priority inheritance bugs**
   - **Mitigation:** Extensive unit testing
   - **Contingency:** Disable priority inheritance if bugs found

3. **Resurrection server false positives**
   - **Mitigation:** Conservative timeout values
   - **Contingency:** Make resurrection optional (compile flag)

4. **Performance regression**
   - **Mitigation:** Continuous benchmarking
   - **Contingency:** Keep legacy spinlock as fallback

5. **Integration conflicts with existing code**
   - **Mitigation:** Feature flags for gradual rollout
   - **Contingency:** Parallel development, merge later

### Contingency Plans

If Phase 1 takes longer than expected:
- Simplify NUMA detection (use heuristics only)
- Skip hierarchical queuing, implement later

If Phase 2 blocks:
- Implement basic adaptive (no priority inheritance)
- Add priority inheritance in Phase 2.5

If Phases run ahead of schedule:
- Add extra features (read-write locks, sequence locks)
- More comprehensive benchmarking
- Academic paper preparation

---

## Resource Requirements

### Development Tools
- [x] CMake build system
- [x] Ninja (fast builds)
- [x] Clang 18 (C17 support)
- [x] GDB (debugging)
- [ ] perf (profiling) - install if needed
- [ ] valgrind (memory checking) - install if needed
- [ ] gnuplot (graphing benchmarks) - install if needed

### Testing Infrastructure
- [x] QEMU x86_64
- [ ] QEMU with NUMA configuration
- [ ] Automated test harness
- [ ] CI/CD integration (optional)

### Documentation Tools
- [ ] Doxygen (API docs)
- [ ] Markdown renderer
- [ ] LaTeX (for academic paper, optional)

### Time Commitment
- **Total:** 12 weeks × 20 hours/week = 240 hours
- **Phase 1:** 35 hours
- **Phase 2:** 45 hours
- **Phase 3:** 36 hours
- **Phase 4:** 30 hours
- **Phase 5:** 38 hours
- **Phase 6:** 40 hours
- **Integration:** 20 hours
- **Documentation:** 16 hours
- **Buffer:** 20 hours (for unexpected issues)

---

## Next Steps

**Immediate (This Session):**
1. [x] Create this roadmap document
2. [ ] Update TODO list
3. [ ] Begin Step 1.1.1 (NUMA topology detection)

**Tomorrow:**
1. Complete Step 1.1.1
2. Begin Step 1.1.2 (Hierarchical MCS queue)

**This Week:**
1. Complete Phase 1 foundation
2. Begin Phase 1 testing

**This Month:**
1. Complete Phases 1-2
2. Begin Phase 3

---

## Tracking Progress

Use the TODO list to track daily progress. Update this roadmap weekly with:
- Completed tasks (mark with ✓)
- Actual time spent vs estimated
- Blockers encountered
- Adjustments to plan

**Weekly Review Questions:**
1. What did we complete this week?
2. Are we on schedule?
3. Any blockers?
4. Adjustments needed?
5. What's the focus for next week?

---

**Document Version:** 1.0
**Last Updated:** 2025-11-17
**Status:** Active Development - Phase 1 Started
**Next Milestone:** Complete qspinlock NUMA topology detection (Step 1.1.1)
