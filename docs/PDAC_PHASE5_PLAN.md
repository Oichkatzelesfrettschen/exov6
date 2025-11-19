# PDAC Phase 5 Implementation Plan: Lock-Free Concurrency & NUMA Revolution

**Date**: 2025-11-19
**Status**: Architectural Design Phase
**Objective**: Transform PDAC into a cutting-edge lock-free, NUMA-aware system
**Estimated Duration**: ~40 hours
**Revolutionary Goal**: Zero-lock scalability with novel concurrent data structures

---

## Executive Summary

Phase 5 **revolutionizes** PDAC's concurrency model by eliminating locks and introducing state-of-the-art concurrent algorithms. This represents a **fundamental redesign** of the system's core data structures.

### The Scalability Crisis

**Current PDAC (Phase 4)**:
- Per-CPU queues: Good (isolated state)
- But: Load balancing requires locks
- DAG updates: Potential lock contention
- Capability table: Lock-protected

**At scale** (16+ CPUs):
- Lock contention becomes bottleneck
- Cache coherence traffic explodes
- Scalability plateaus around 8-12 CPUs

**Solution**: **Lock-free data structures + RCU + Work-stealing**

---

## Phase 5 Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    LOCK-FREE PDAC v2.0                       │
├─────────────────────────────────────────────────────────────┤
│                                                               │
│  ┌───────────────────────────────────────────────────────┐  │
│  │   NUMA-Aware Topology                                 │  │
│  │   - Per-node schedulers                               │  │
│  │   - Local memory allocation                           │  │
│  │   - Cross-node migration policies                     │  │
│  └───────────────────────────────────────────────────────┘  │
│                          │                                   │
│  ┌───────────────────────┼───────────────────────────────┐  │
│  │                       │                               │  │
│  │  ┌─────────────┐  ┌───▼──────────┐  ┌─────────────┐ │  │
│  │  │ NUMA Node 0 │  │ NUMA Node 1  │  │ NUMA Node 2 │ │  │
│  │  │             │  │              │  │             │ │  │
│  │  │ ┌─────────┐ │  │ ┌─────────┐  │  │ ┌─────────┐ │ │  │
│  │  │ │CPU 0-3  │ │  │ │CPU 4-7  │  │  │ │CPU 8-11 │ │ │  │
│  │  │ │         │ │  │ │         │  │  │ │         │ │ │  │
│  │  │ │ ┌─────┐ │ │  │ │ ┌─────┐ │  │  │ │ ┌─────┐ │ │ │  │
│  │  │ │ │Work │ │ │  │ │ │Work │ │  │  │ │ │Work │ │ │ │  │
│  │  │ │ │Steal│ │ │  │ │ │Steal│ │  │  │ │ │Steal│ │ │ │  │
│  │  │ │ │Deque│ │ │  │ │ │Deque│ │  │  │ │ │Deque│ │ │ │  │
│  │  │ │ └─────┘ │ │  │ │ └─────┘ │  │  │ │ └─────┘ │ │ │  │
│  │  │ └─────────┘ │  │ └─────────┘  │  │ └─────────┘ │ │  │
│  │  │             │  │              │  │             │ │  │
│  │  │  Local Mem  │  │  Local Mem   │  │  Local Mem  │ │  │
│  │  └─────────────┘  └──────────────┘  └─────────────┘ │  │
│  └───────────────────────────────────────────────────────┘  │
│                          │                                   │
│  ┌───────────────────────▼───────────────────────────────┐  │
│  │   RCU-Protected Shared State                          │  │
│  │   - DAG structure (RCU read-side)                     │  │
│  │   - Capability table (hazard pointers)                │  │
│  │   - Global telemetry (lock-free counters)             │  │
│  └───────────────────────────────────────────────────────┘  │
│                          │                                   │
│  ┌───────────────────────▼───────────────────────────────┐  │
│  │   Lock-Free Primitives                                │  │
│  │   - Michael-Scott queue (MPMC)                        │  │
│  │   - Treiber stack (LIFO)                              │  │
│  │   - Chase-Lev deque (work-stealing)                   │  │
│  │   - Hazard pointers (memory reclamation)              │  │
│  │   - Atomic counters (telemetry)                       │  │
│  └───────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

---

## Revolutionary Changes

### 1. Lock-Free Data Structures

Replace all lock-protected structures with lock-free counterparts.

**Michael-Scott Queue** (MPMC):
```c
typedef struct ms_node {
    void *data;
    atomic_ptr_t next;
} ms_node_t;

typedef struct ms_queue {
    atomic_ptr_t head;
    atomic_ptr_t tail;
    hazard_pointer_t *hp;  // Memory reclamation
} ms_queue_t;
```

**Operations**:
- Enqueue: O(1) lock-free
- Dequeue: O(1) lock-free
- No ABA problem (hazard pointers)

**Treiber Stack** (LIFO):
```c
typedef struct treiber_node {
    void *data;
    atomic_ptr_t next;
} treiber_node_t;

typedef struct treiber_stack {
    atomic_ptr_t top;
    hazard_pointer_t *hp;
} treiber_stack_t;
```

**Chase-Lev Work-Stealing Deque**:
```c
typedef struct chase_lev_deque {
    atomic_ptr_t array;      // Circular buffer
    atomic_size_t top;       // Owner pops here
    atomic_size_t bottom;    // Owner pushes here
} chase_lev_deque_t;
```

**Key Property**: Owner operations are wait-free, steals are lock-free!

### 2. RCU (Read-Copy-Update)

Replace reader-writer locks with RCU for DAG traversal.

**RCU Principles**:
- Readers never block (super-fast)
- Writers copy-modify-update
- Grace period ensures safety

**RCU API**:
```c
// Read-side critical section
void rcu_read_lock(void);
void rcu_read_unlock(void);

// Updater-side
void *rcu_dereference(void **ptr);
void rcu_assign_pointer(void **ptr, void *val);

// Synchronization
void synchronize_rcu(void);          // Wait for grace period
void call_rcu(rcu_head_t *head, rcu_callback_t func);  // Async
```

**DAG with RCU**:
```c
typedef struct dag_task_rcu {
    dag_task_t task;
    rcu_head_t rcu;  // For deferred freeing
} dag_task_rcu_t;

// Read DAG task (lock-free!)
dag_task_t *dag_read_task(dag_pdac_t *dag, uint16_t id) {
    rcu_read_lock();
    dag_task_t *task = rcu_dereference(&dag->tasks[id]);
    // Use task...
    rcu_read_unlock();
    return task;
}

// Update DAG task
void dag_update_task(dag_pdac_t *dag, uint16_t id, dag_task_t *new_task) {
    dag_task_t *old = dag->tasks[id];
    rcu_assign_pointer(&dag->tasks[id], new_task);
    call_rcu(&old->rcu, free_task_callback);  // Deferred free
}
```

**Benefits**:
- Readers: Zero synchronization overhead
- Writers: Only compete with each other
- Scalability: Near-linear with CPU count

### 3. Work-Stealing Scheduler

Replace periodic load balancing with continuous work-stealing.

**Chase-Lev Algorithm**:
- Each CPU has own deque
- Owner: LIFO (cache-friendly)
- Thieves: FIFO (load balance)

**Stealing Protocol**:
```c
// Owner (fast path)
task_t *local_pop() {
    size_t b = deque->bottom - 1;
    atomic_store(&deque->bottom, b);

    size_t t = atomic_load(&deque->top);
    if (t <= b) {
        // Queue not empty
        task_t *task = array[b % size];
        if (t == b) {
            // Last item - CAS with thieves
            if (!CAS(&deque->top, t, t+1)) {
                task = NULL;  // Stolen
            }
            atomic_store(&deque->bottom, b+1);
        }
        return task;
    }
    atomic_store(&deque->bottom, b+1);
    return NULL;  // Empty
}

// Thief (from another CPU)
task_t *steal(deque_t *victim) {
    size_t t = atomic_load(&victim->top);
    size_t b = atomic_load(&victim->bottom);

    if (t < b) {
        task_t *task = array[t % size];
        if (CAS(&victim->top, t, t+1)) {
            return task;  // Stolen successfully
        }
    }
    return NULL;  // Failed or empty
}
```

**Stealing Strategy**:
```c
// When idle, try to steal
task_t *find_work(cpu_id) {
    // 1. Try local deque (fast)
    task = local_pop(cpus[cpu_id].deque);
    if (task) return task;

    // 2. Random stealing (avoid hot-spotting)
    for (int i = 0; i < num_cpus; i++) {
        int victim = (cpu_id + random()) % num_cpus;
        task = steal(cpus[victim].deque);
        if (task) return task;
    }

    return NULL;  // No work found
}
```

**Advantages**:
- Continuous (not periodic)
- Localized (owner operations fast)
- Randomized (no hot spots)

### 4. NUMA Awareness

Optimize for Non-Uniform Memory Access.

**NUMA Topology**:
```c
typedef struct numa_node {
    uint8_t node_id;
    uint8_t cpu_ids[16];     // CPUs in this node
    uint8_t num_cpus;

    // Memory info
    uint64_t local_memory_mb;
    uint64_t free_memory_mb;

    // Distance matrix
    uint8_t distance[MAX_NUMA_NODES];  // Latency to other nodes
} numa_node_t;

typedef struct numa_topology {
    numa_node_t nodes[MAX_NUMA_NODES];
    uint8_t num_nodes;
} numa_topology_t;
```

**NUMA-Aware Allocation**:
```c
void *numa_alloc_local(size_t size) {
    int cpu = get_current_cpu();
    int node = cpu_to_node[cpu];
    return allocate_on_node(node, size);
}

void *numa_alloc_on_node(int node, size_t size);
void numa_free(void *ptr);
```

**NUMA-Aware Scheduling**:
```c
// Prefer local node for task execution
int numa_find_cpu(task_t *task) {
    int preferred_node = task->numa_node;

    // Try local node first
    for (int i = 0; i < nodes[preferred_node].num_cpus; i++) {
        int cpu = nodes[preferred_node].cpu_ids[i];
        if (cpu_is_idle(cpu)) {
            return cpu;
        }
    }

    // Fall back to closest node
    for (int distance = 1; distance < num_nodes; distance++) {
        for (int node = 0; node < num_nodes; node++) {
            if (nodes[preferred_node].distance[node] == distance) {
                // Try this node...
            }
        }
    }

    return -1;  // No CPU found
}
```

**Cross-Node Migration Policy**:
```
Only migrate if:
  (remote_queue_length - local_queue_length) > THRESHOLD
  AND
  (migration_cost < expected_benefit)

Where:
  migration_cost = cross_node_latency × data_size
  expected_benefit = (wait_time_saved) × task_priority
```

### 5. Hazard Pointers (Memory Reclamation)

Safe memory reclamation for lock-free structures.

**Hazard Pointer Record**:
```c
typedef struct hazard_pointer {
    atomic_ptr_t ptr;        // Protected pointer
    atomic_int active;       // Is this HP in use?
} hazard_pointer_t;

typedef struct hp_domain {
    hazard_pointer_t hps[MAX_THREADS * HP_PER_THREAD];
    atomic_ptr_t retire_list;  // Retired nodes
} hp_domain_t;
```

**Usage Protocol**:
```c
// 1. Acquire hazard pointer
void *hp_protect(void **src) {
    int tid = get_thread_id();
    hazard_pointer_t *hp = &hps[tid];

    void *ptr;
    do {
        ptr = atomic_load(src);
        atomic_store(&hp->ptr, ptr);
    } while (ptr != atomic_load(src));  // Retry if changed

    return ptr;
}

// 2. Release hazard pointer
void hp_clear(int tid) {
    atomic_store(&hps[tid].ptr, NULL);
}

// 3. Retire node
void hp_retire(void *ptr) {
    add_to_retire_list(ptr);

    if (retire_list_size > THRESHOLD) {
        hp_scan();  // Try to free some
    }
}

// 4. Scan and free
void hp_scan() {
    // Collect all active hazard pointers
    set<void*> protected;
    for (hp in hps) {
        if (hp->active) {
            protected.insert(hp->ptr);
        }
    }

    // Free retired nodes not in protected set
    for (node in retire_list) {
        if (!protected.contains(node)) {
            free(node);
        }
    }
}
```

---

## Novel Algorithms & Data Structures

### 1. Octonion-Weighted Work-Stealing

**Innovation**: Use octonion norm for stealing decisions.

```c
// Steal from victim with highest resource imbalance
int choose_steal_victim() {
    double max_imbalance = 0;
    int victim = -1;

    for (int i = 0; i < num_cpus; i++) {
        if (i == my_cpu) continue;

        // Compute resource imbalance using octonion norm
        resource_vector_t my_res = compute_cpu_resources(my_cpu);
        resource_vector_t victim_res = compute_cpu_resources(i);

        resource_vector_t diff = resource_vector_subtract(victim_res, my_res);
        q16_t imbalance = resource_vector_norm(diff);

        if (imbalance > max_imbalance) {
            max_imbalance = imbalance;
            victim = i;
        }
    }

    return victim;
}
```

**Benefit**: Balances across all 8 dimensions, not just queue length!

### 2. RCU-Protected Capability Table

**Innovation**: Lock-free capability lookups.

```c
typedef struct capability_v3 {
    capability_v2_t cap;      // Original capability
    rcu_head_t rcu;           // For RCU
    atomic_int refcount;      // Reference counting
} capability_v3_t;

// Lock-free lookup (read-side)
capability_v3_t *cap_lookup_lockfree(int slot) {
    rcu_read_lock();
    capability_v3_t *cap = rcu_dereference(&cap_table[slot]);
    atomic_inc(&cap->refcount);  // Prevent premature free
    rcu_read_unlock();
    return cap;
}

// Lock-free revoke (write-side)
void cap_revoke_lockfree(int slot) {
    capability_v3_t *old_cap = cap_table[slot];
    capability_v3_t *revoked = create_revoked_cap();

    rcu_assign_pointer(&cap_table[slot], revoked);

    call_rcu(&old_cap->rcu, [](rcu_head_t *head) {
        capability_v3_t *cap = container_of(head, capability_v3_t, rcu);
        if (atomic_dec_and_test(&cap->refcount)) {
            free(cap);
        }
    });
}
```

### 3. Adaptive Work-Stealing Threshold

**Innovation**: Self-tuning based on contention.

```c
typedef struct adaptive_ws {
    atomic_int steal_attempts;
    atomic_int steal_successes;
    atomic_int steal_threshold;  // Dynamic threshold

    uint64_t last_adjust_time;
} adaptive_ws_t;

void adjust_steal_threshold(adaptive_ws_t *ws) {
    double success_rate = (double)ws->steal_successes / ws->steal_attempts;

    if (success_rate < 0.3) {
        // Too much contention - increase threshold
        atomic_fetch_add(&ws->steal_threshold, 1);
    } else if (success_rate > 0.7) {
        // Not enough stealing - decrease threshold
        atomic_fetch_sub(&ws->steal_threshold, 1);
    }

    // Clamp to [MIN, MAX]
    int threshold = atomic_load(&ws->steal_threshold);
    if (threshold < MIN_THRESHOLD) threshold = MIN_THRESHOLD;
    if (threshold > MAX_THRESHOLD) threshold = MAX_THRESHOLD;
    atomic_store(&ws->steal_threshold, threshold);
}

bool should_steal() {
    int local_queue_size = get_local_queue_size();
    int threshold = atomic_load(&ws_state.steal_threshold);

    return local_queue_size < threshold;
}
```

### 4. NUMA-Aware Beatty Sequences

**Innovation**: Use different α per NUMA node.

```c
typedef struct numa_beatty {
    q16_t alpha[MAX_NUMA_NODES];  // Different ratio per node
    uint64_t counters[MAX_NUMA_NODES];
} numa_beatty_t;

// Node 0: φ = 1.618 (golden ratio)
// Node 1: √2 = 1.414 (silver ratio)
// Node 2: √3 = 1.732
// Node 3: √5 = 2.236

task_t *numa_beatty_select(int node) {
    uint64_t beatty = (counters[node] * alpha[node]) >> 16;
    counters[node]++;

    return tasks_on_node[node][beatty % num_tasks_on_node[node]];
}
```

**Benefit**: Different nodes explore task space differently, increasing diversity!

---

## Implementation Roadmap

### Phase 5.1: Lock-Free Primitives (8 hours)

**Task 5.1.1: Michael-Scott Queue** (2 hours)
- Implement MPMC lock-free queue
- Hazard pointer integration
- Test: Concurrent enqueue/dequeue

**Task 5.1.2: Treiber Stack** (1.5 hours)
- Implement LIFO stack
- ABA protection
- Test: Concurrent push/pop

**Task 5.1.3: Hazard Pointers** (3 hours)
- Implement HP domain
- Protection protocol
- Retirement and scanning
- Test: Memory safety under concurrency

**Task 5.1.4: Tests** (1.5 hours)
- Linearizability tests
- Stress tests (high contention)
- Performance benchmarks

### Phase 5.2: RCU Framework (10 hours)

**Task 5.2.1: Grace Period Tracking** (3 hours)
- Quiescent state detection
- Per-CPU grace period counters
- Global synchronization

**Task 5.2.2: Read-Side API** (2 hours)
- rcu_read_lock/unlock
- rcu_dereference
- Preemption tracking

**Task 5.2.3: Update-Side API** (3 hours)
- rcu_assign_pointer
- synchronize_rcu (blocking)
- call_rcu (callback-based)

**Task 5.2.4: DAG Integration** (1.5 hours)
- Convert DAG reads to RCU
- Update protocol for DAG modifications

**Task 5.2.5: Tests** (0.5 hours)
- Grace period correctness
- Concurrent read/update
- Memory ordering

### Phase 5.3: Work-Stealing Scheduler (12 hours)

**Task 5.3.1: Chase-Lev Deque** (4 hours)
- Circular buffer with atomic operations
- Owner push/pop (wait-free)
- Thief steal (lock-free)
- Dynamic resizing

**Task 5.3.2: Work-Stealing Scheduler** (4 hours)
- Random stealing strategy
- Victim selection (octonion-weighted)
- Adaptive threshold

**Task 5.3.3: Task Migration** (2 hours)
- Migration protocol
- State transfer
- Affinity tracking

**Task 5.3.4: Integration** (1.5 hours)
- Replace load balancing with work-stealing
- Hybrid scheduler integration

**Task 5.3.5: Tests** (0.5 hours)
- Stealing correctness
- Load balance verification
- Performance vs. old scheduler

### Phase 5.4: NUMA Awareness (10 hours)

**Task 5.4.1: Topology Detection** (2 hours)
- NUMA node discovery (simulated)
- Distance matrix
- CPU-to-node mapping

**Task 5.4.2: NUMA Allocator** (3 hours)
- Per-node memory pools
- Local allocation
- Remote fallback

**Task 5.4.3: NUMA Scheduling** (3 hours)
- Node affinity
- Cross-node migration policy
- NUMA-aware Beatty

**Task 5.4.4: Cross-Node Migration** (1.5 hours)
- Cost-benefit analysis
- Migration thresholds

**Task 5.4.5: Tests** (0.5 hours)
- Locality verification
- Migration overhead measurement

### Phase 5.5: Refactoring & Optimization (6 hours)

**Task 5.5.1: Capability Refactoring** (2 hours)
- Convert to RCU-protected
- Lock-free lookups

**Task 5.5.2: Scheduler State** (2 hours)
- Atomic counters for telemetry
- Lock-free statistics

**Task 5.5.3: Hot Path Optimization** (1.5 hours)
- Profile critical paths
- Cache-line alignment
- Prefetching hints

**Task 5.5.4: Adaptive Tuning** (0.5 hours)
- Self-tuning steal threshold
- Dynamic NUMA migration

### Phase 5.6: Examples (3 hours)
- 10 comprehensive examples covering all new features

### Phase 5.7: Testing (4 hours)
- 30+ concurrency tests
- Linearizability checking
- Performance regression tests

### Phase 5.8: Documentation (3 hours)
- Phase 5 architecture guide
- Lock-free programming tutorial
- Performance analysis

**Total**: ~40 hours

---

## Performance Targets

| Metric | Phase 4 | Phase 5 Target | Improvement |
|--------|---------|----------------|-------------|
| **Latency** (16 CPUs) | 12 μs | 7 μs | 1.7x faster |
| **Throughput** (16 CPUs) | 500K/sec | 2M/sec | 4x higher |
| **Scalability** (strong) | 8 CPUs | 16+ CPUs | 2x scale |
| **Lock contention** | Medium | Zero | ∞ |
| **NUMA efficiency** | N/A | 90%+ | New |

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Lock-free bugs | High | Critical | Extensive testing, model checking |
| Memory leaks (HP) | Medium | High | Valgrind, stress tests |
| Performance regression | Low | Medium | Benchmarks, profiling |
| Complexity increase | High | Medium | Comprehensive docs |
| RCU grace period stalls | Medium | High | Timeout detection |

---

## Success Criteria

✅ **Zero locks** in critical paths
✅ **Linear scalability** to 16 CPUs
✅ **< 10 μs latency** at 16 CPUs
✅ **90%+ NUMA locality** for local tasks
✅ **All tests passing** (including concurrency stress)
✅ **Comprehensive documentation** for lock-free concepts

---

**Status**: ✅ Architecture Complete - Ready for Implementation
**Next Step**: Begin Task 5.1.1 (Michael-Scott Queue)
