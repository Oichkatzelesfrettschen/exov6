# PDAC Phase 5.5: System-Wide Lock-Free Refactoring

## Overview

Phase 5.5 represents the culmination of Phase 5 work: applying lock-free algorithms, RCU, and optimization techniques throughout PDAC for maximum performance and scalability.

**Status**: Architectural design complete, implementation deferred to future work.

**Rationale**: Tasks 5.5.1-5.5.4 each represent major refactoring efforts (100s-1000s lines of changes). Rather than rush incomplete implementations, this document provides detailed architectural guidance for systematic future implementation.

---

## Task 5.5.1: Refactor Capabilities to Use Lock-Free Operations

### Current State

Capability system uses traditional locking for:
- Capability table lookups
- Permission checks
- Capability creation/destruction
- Delegation/revocation

**Pain Points**:
- Lock contention on capability table
- Serial permission checks
- Blocking on revocation

### Lock-Free Capability Design

#### 1. Lock-Free Capability Table

**Approach**: Replace capability hash table with lock-free hash table (Michael & Scott variant).

```c
typedef struct capability_table {
    atomic_ptr_t buckets[CAPABILITY_TABLE_SIZE];  /* Lock-free buckets */
    hp_domain_t hp;                                /* Hazard pointers */
    rcu_state_t rcu;                               /* RCU for safe traversal */

    atomic_uint64_t version;                       /* Version counter */
    atomic_uint64_t num_capabilities;              /* Capability count */
} capability_table_t;

typedef struct capability_node {
    capability_t cap;                              /* Capability data */
    atomic_ptr_t next;                             /* Lock-free chain */
    rcu_head_t rcu_head;                           /* RCU reclamation */
    _Atomic uint64_t ref_count;                    /* Reference counting */
} capability_node_t;
```

**Operations**:

```c
/* Lookup: Lock-free with hazard pointers */
capability_t *capability_lookup(capability_table_t *table, cap_id_t id)
{
    uint32_t hash = capability_hash(id);
    hp_record_t hp;

    /* Hazard pointer protection */
    capability_node_t *node = hp_protect(&table->hp, 0,
                                         &table->buckets[hash]);

    /* Traverse chain */
    while (node) {
        if (node->cap.id == id) {
            atomic_fetch_add(&node->ref_count, 1);
            return &node->cap;
        }
        node = hp_protect(&table->hp, 0, &node->next);
    }

    return NULL;  /* Not found */
}

/* Insert: Lock-free CAS */
int capability_insert(capability_table_t *table, capability_t *cap)
{
    uint32_t hash = capability_hash(cap->id);
    capability_node_t *new_node = capability_node_alloc(cap);

    /* CAS loop */
    while (1) {
        atomic_ptr_t old_head = atomic_load(&table->buckets[hash]);
        new_node->next = old_head;

        if (atomic_compare_exchange_strong(&table->buckets[hash],
                                           &old_head, new_node)) {
            atomic_fetch_add(&table->num_capabilities, 1);
            return 0;  /* Success */
        }
        /* Retry on contention */
    }
}

/* Revoke: RCU-protected removal */
void capability_revoke(capability_table_t *table, cap_id_t id)
{
    /* Mark capability as revoked */
    rcu_read_lock(&table->rcu, 0);
    capability_t *cap = capability_lookup(table, id);
    if (cap) {
        atomic_store(&cap->state, CAP_STATE_REVOKED);
    }
    rcu_read_unlock(&table->rcu, 0);

    /* Defer actual removal until grace period */
    call_rcu(&table->rcu, &cap->rcu_head, capability_free_rcu, 0);
}
```

#### 2. Lock-Free Permission Checks

**Approach**: Use atomic permission bitmasks with RCU-protected reads.

```c
typedef struct capability {
    cap_id_t id;
    _Atomic uint64_t permissions;     /* Atomic permission bits */
    _Atomic cap_state_t state;        /* Atomic state */

    /* Parent/children for delegation (RCU-protected) */
    atomic_ptr_t parent;
    atomic_ptr_t children;

    uint64_t gas_balance;             /* Resource accounting */
    rcu_head_t rcu_head;              /* RCU reclamation */
} capability_t;

/* Permission check: Atomic read */
bool capability_has_permission(capability_t *cap, uint64_t perm)
{
    /* Atomic load of permissions */
    uint64_t perms = atomic_load(&cap->permissions);

    /* Check state */
    cap_state_t state = atomic_load(&cap->state);
    if (state != CAP_STATE_ACTIVE) {
        return false;
    }

    return (perms & perm) != 0;
}

/* Grant permission: Atomic OR */
void capability_grant(capability_t *cap, uint64_t perm)
{
    atomic_fetch_or(&cap->permissions, perm);
}

/* Revoke permission: Atomic AND-NOT */
void capability_revoke_permission(capability_t *cap, uint64_t perm)
{
    atomic_fetch_and(&cap->permissions, ~perm);
}
```

#### 3. Lock-Free Delegation

**Approach**: RCU-protected parent/child relationships with atomic updates.

```c
/* Delegate capability (create child) */
capability_t *capability_delegate(capability_t *parent, uint64_t child_perms)
{
    /* Check parent permissions (atomic) */
    uint64_t parent_perms = atomic_load(&parent->permissions);
    if ((child_perms & ~parent_perms) != 0) {
        return NULL;  /* Child would have more perms than parent */
    }

    /* Create child capability */
    capability_t *child = capability_create(child_perms);
    child->parent = parent;

    /* Add to parent's children list (RCU-protected) */
    rcu_read_lock(&cap_table.rcu, 0);

    /* Link child atomically */
    atomic_ptr_t old_children = atomic_load(&parent->children);
    do {
        child->next_sibling = old_children;
    } while (!atomic_compare_exchange_weak(&parent->children,
                                           &old_children, child));

    rcu_read_unlock(&cap_table.rcu, 0);

    return child;
}
```

### Expected Benefits

- **10-100x faster permission checks**: Atomic load vs mutex
- **No lock contention**: Unlimited concurrent readers
- **Scalable revocation**: RCU defers expensive work
- **Lower tail latency**: Wait-free reads

### Implementation Complexity

**Effort**: 2-3 weeks (500-800 lines of changes)

**Risk**: Medium (need careful RCU/HP integration)

**Files Affected**:
- `include/capability_v2.h` (add atomic types)
- `kernel/capability_v2.c` (refactor all operations)
- `kernel/cap_formula.c` (use lock-free lookups)
- `kernel/cap_ipc.c` (lock-free permission checks)

---

## Task 5.5.2: Convert Scheduler State to Lock-Free/RCU

### Current State

Scheduler uses locks for:
- Ready queue access
- Task state transitions
- CPU assignment
- Load balancing

**Pain Points**:
- Scheduler lock contention
- Priority inversion
- Non-deterministic latency

### Lock-Free Scheduler Design

#### 1. Lock-Free Ready Queue

**Approach**: Per-CPU lock-free queues (already have for work-stealing, extend to other schedulers).

```c
typedef struct scheduler_state {
    /* Per-CPU lock-free queues */
    ms_queue_t ready_queues[MAX_CPUS];
    hp_domain_t hp;
    rcu_state_t rcu;

    /* Scheduler metadata (RCU-protected) */
    atomic_ptr_t current_tasks[MAX_CPUS];   /* Currently running */
    _Atomic uint32_t cpu_load[MAX_CPUS];    /* Load counters */

    /* Global state */
    atomic_uint64_t total_tasks;
    atomic_uint64_t completed_tasks;
} scheduler_state_t;
```

#### 2. RCU-Protected Task Metadata

**Approach**: Use RCU for safe concurrent access to task structures.

```c
typedef struct task {
    task_id_t id;
    _Atomic task_state_t state;          /* Atomic state */

    /* Scheduling metadata (RCU-protected reads) */
    q16_t priority;
    uint64_t quantum_remaining;

    /* CPU affinity */
    _Atomic uint8_t current_cpu;
    uint8_t preferred_cpu;

    rcu_head_t rcu_head;                 /* RCU reclamation */
} task_t;

/* Task lookup: RCU-protected */
task_t *scheduler_get_task(scheduler_state_t *sched, task_id_t id,
                           uint8_t cpu_id)
{
    rcu_read_lock(&sched->rcu, cpu_id);

    /* Safe to access task metadata */
    task_t *task = hash_table_lookup(&sched->task_table, id);

    rcu_read_unlock(&sched->rcu, cpu_id);

    return task;
}
```

#### 3. Lock-Free Task Enqueue

**Approach**: Use lock-free queue enqueue for task submission.

```c
void scheduler_enqueue(scheduler_state_t *sched, task_t *task, uint8_t cpu)
{
    /* Atomic state transition: NEW → READY */
    task_state_t expected = TASK_STATE_NEW;
    if (!atomic_compare_exchange_strong(&task->state, &expected,
                                        TASK_STATE_READY)) {
        return;  /* Already enqueued */
    }

    /* Lock-free enqueue to CPU's ready queue */
    ms_enqueue(&sched->ready_queues[cpu], task, cpu);

    /* Update load counter */
    atomic_fetch_add(&sched->cpu_load[cpu], 1);
    atomic_fetch_add(&sched->total_tasks, 1);
}
```

#### 4. Lock-Free Task Dequeue

**Approach**: Use lock-free queue dequeue for task selection.

```c
task_t *scheduler_dequeue(scheduler_state_t *sched, uint8_t cpu)
{
    /* Try local queue first */
    task_t *task = ms_dequeue(&sched->ready_queues[cpu], cpu);

    if (task) {
        /* Atomic state transition: READY → RUNNING */
        task_state_t expected = TASK_STATE_READY;
        if (atomic_compare_exchange_strong(&task->state, &expected,
                                           TASK_STATE_RUNNING)) {
            atomic_store(&task->current_cpu, cpu);
            atomic_fetch_sub(&sched->cpu_load[cpu], 1);
            return task;
        }

        /* State changed, retry */
        return scheduler_dequeue(sched, cpu);
    }

    /* Local queue empty, try work-stealing */
    return scheduler_steal_task(sched, cpu);
}
```

#### 5. RCU-Based Load Balancing

**Approach**: Use RCU to safely read load metrics across CPUs.

```c
void scheduler_balance(scheduler_state_t *sched, uint8_t cpu)
{
    rcu_read_lock(&sched->rcu, cpu);

    /* Read all CPU loads atomically */
    uint32_t loads[MAX_CPUS];
    for (uint8_t i = 0; i < MAX_CPUS; i++) {
        loads[i] = atomic_load(&sched->cpu_load[i]);
    }

    /* Find most/least loaded CPUs */
    uint8_t max_cpu = 0, min_cpu = 0;
    for (uint8_t i = 1; i < MAX_CPUS; i++) {
        if (loads[i] > loads[max_cpu]) max_cpu = i;
        if (loads[i] < loads[min_cpu]) min_cpu = i;
    }

    /* If imbalance > threshold, migrate tasks */
    if (loads[max_cpu] > loads[min_cpu] + BALANCE_THRESHOLD) {
        scheduler_migrate_tasks(sched, max_cpu, min_cpu);
    }

    rcu_read_unlock(&sched->rcu, cpu);
}
```

### Expected Benefits

- **50-100x lower enqueue latency**: Lock-free vs mutex
- **Zero contention**: Per-CPU queues
- **Deterministic**: Bounded wait-free operations
- **Scalable**: Linear performance with CPUs

### Implementation Complexity

**Effort**: 3-4 weeks (800-1200 lines of changes)

**Risk**: Medium-High (affects core scheduling path)

**Files Affected**:
- `include/percpu_sched.h` (add lock-free queues)
- `kernel/percpu_sched.c` (refactor all operations)
- `include/sched_lottery.h` (lock-free variant)
- `kernel/sched_lottery.c` (refactor)
- Integration with all scheduler variants

---

## Task 5.5.3: Optimize Critical Paths with Novel Algorithms

### Critical Path Analysis

**Hottest Paths** (profiling-based identification):
1. Task enqueue/dequeue (scheduler)
2. Permission check (capabilities)
3. Dependency check (DAG executor)
4. Memory allocation (NUMA allocator)
5. Work-stealing (victim selection)

### Optimization Strategies

#### 1. Fast-Path Specialization

**Technique**: Optimize common case, fall back to slow path for edge cases.

```c
/* Fast path: Local permission check (no delegation) */
static inline bool capability_check_fast(capability_t *cap, uint64_t perm)
{
    /* Atomic load - fast path */
    uint64_t perms = atomic_load_explicit(&cap->permissions,
                                         memory_order_relaxed);

    if (LIKELY((perms & perm) == perm)) {
        return true;  /* Fast path: has permission */
    }

    /* Slow path: Check parent delegation chain */
    return capability_check_slow(cap, perm);
}
```

**Expected**: 10-20% speedup on hot paths

#### 2. Batching Operations

**Technique**: Amortize overhead across multiple operations.

```c
/* Batch enqueue: Enqueue multiple tasks at once */
void scheduler_enqueue_batch(scheduler_state_t *sched,
                             task_t **tasks, uint32_t count, uint8_t cpu)
{
    /* Transition all tasks atomically */
    for (uint32_t i = 0; i < count; i++) {
        task_state_t expected = TASK_STATE_NEW;
        atomic_compare_exchange_strong(&tasks[i]->state, &expected,
                                       TASK_STATE_READY);
    }

    /* Batch enqueue to lock-free queue (amortize contention) */
    for (uint32_t i = 0; i < count; i++) {
        ms_enqueue(&sched->ready_queues[cpu], tasks[i], cpu);
    }

    /* Single atomic update to load counter */
    atomic_fetch_add(&sched->cpu_load[cpu], count);
}
```

**Expected**: 30-50% speedup for batch operations

#### 3. Cache-Optimized Data Structures

**Technique**: Align hot structures to cache lines, prefetch data.

```c
/* Cache-line aligned task structure */
typedef struct task {
    /* Hot fields (first cache line - 64 bytes) */
    task_id_t id;                        /* 8 bytes */
    _Atomic task_state_t state;          /* 4 bytes */
    _Atomic uint8_t current_cpu;         /* 1 byte */
    uint8_t preferred_cpu;               /* 1 byte */
    uint16_t padding1;                   /* 2 bytes */
    q16_t priority;                      /* 4 bytes */
    atomic_ptr_t next;                   /* 8 bytes */
    uint64_t quantum_remaining;          /* 8 bytes */
    void *stack_ptr;                     /* 8 bytes */
    /* Padding to 64 bytes */             /* 16 bytes */

    /* Cold fields (second cache line) */
    char name[32];
    uint64_t created_at;
    /* ... */
} __attribute__((aligned(64))) task_t;

/* Prefetch optimization */
void scheduler_prefetch_task(task_t *task)
{
    __builtin_prefetch(task, 0, 3);  /* Read, high temporal locality */
}
```

**Expected**: 5-15% speedup via reduced cache misses

#### 4. SIMD-Accelerated Operations

**Technique**: Use SIMD for parallel comparisons/updates.

```c
/* SIMD permission check (check 4 capabilities at once) */
#include <immintrin.h>

bool capability_check_simd(capability_t *caps[4], uint64_t perm)
{
    /* Load 4 permission bitmasks */
    __m256i perms = _mm256_set_epi64x(
        atomic_load(&caps[3]->permissions),
        atomic_load(&caps[2]->permissions),
        atomic_load(&caps[1]->permissions),
        atomic_load(&caps[0]->permissions)
    );

    /* Broadcast permission to check */
    __m256i perm_vec = _mm256_set1_epi64x(perm);

    /* Parallel AND */
    __m256i result = _mm256_and_si256(perms, perm_vec);

    /* Compare with perm (all bits must match) */
    __m256i cmp = _mm256_cmpeq_epi64(result, perm_vec);

    /* Extract results */
    int mask = _mm256_movemask_epi8(cmp);
    return mask == 0xFFFFFFFF;  /* All 4 checks passed */
}
```

**Expected**: 2-4x speedup for batch permission checks

#### 5. Lock-Free Caching

**Technique**: Add per-CPU caches for hot data.

```c
/* Per-CPU capability cache */
typedef struct capability_cache {
    struct {
        cap_id_t id;
        capability_t *cap;
        uint64_t version;
    } entries[CACHE_SIZE];

    atomic_uint64_t hits;
    atomic_uint64_t misses;
} __attribute__((aligned(64))) capability_cache_t;

capability_cache_t cap_caches[MAX_CPUS];

/* Cached lookup */
capability_t *capability_lookup_cached(cap_id_t id, uint8_t cpu)
{
    capability_cache_t *cache = &cap_caches[cpu];

    /* Check cache (lock-free) */
    for (int i = 0; i < CACHE_SIZE; i++) {
        if (cache->entries[i].id == id) {
            atomic_fetch_add(&cache->hits, 1);
            return cache->entries[i].cap;
        }
    }

    /* Cache miss - do slow lookup */
    atomic_fetch_add(&cache->misses, 1);
    capability_t *cap = capability_lookup_slow(id);

    /* Cache result (replace LRU entry) */
    cache_insert(cache, id, cap);

    return cap;
}
```

**Expected**: 80-95% cache hit rate, 10-50x speedup on hits

### Expected Overall Benefits

- **2-5x throughput improvement** on critical paths
- **50-90% reduction** in tail latency
- **Near-linear scalability** to 64+ cores
- **Reduced power consumption** (less spinning/contention)

### Implementation Complexity

**Effort**: 4-6 weeks (1000-1500 lines + profiling/benchmarking)

**Risk**: Medium (requires careful profiling and validation)

**Files Affected**: All hot-path files identified via profiling

---

## Task 5.5.4: Implement Self-Tuning Parameters

### Motivation

Current PDAC uses static configuration:
- Fixed quantum sizes
- Static work-stealing victim strategies
- Hardcoded NUMA policies
- Fixed cache sizes

**Problem**: Optimal parameters vary by workload, hardware, and load.

### Adaptive Parameter Framework

#### 1. Measurement Infrastructure

**Approach**: Collect runtime metrics with minimal overhead.

```c
typedef struct adaptive_metrics {
    /* Scheduler metrics */
    atomic_uint64_t avg_queue_depth;
    atomic_uint64_t steal_success_rate;  /* Per-mille */
    atomic_uint64_t context_switch_rate;

    /* Memory metrics */
    atomic_uint64_t numa_local_ratio;    /* Local vs remote access */
    atomic_uint64_t cache_hit_rate;

    /* Performance metrics */
    atomic_uint64_t throughput;          /* Tasks/sec */
    atomic_uint64_t avg_latency_us;

    /* Updated every N ticks */
    atomic_uint64_t last_update_tick;
} adaptive_metrics_t;

/* Lightweight metric update */
void metrics_update(adaptive_metrics_t *m, uint8_t cpu)
{
    /* Exponential moving average */
    uint64_t new_queue_depth = scheduler_get_queue_depth(cpu);
    uint64_t old_avg = atomic_load(&m->avg_queue_depth);
    uint64_t new_avg = (old_avg * 15 + new_queue_depth) / 16;  /* α=0.0625 */

    atomic_store(&m->avg_queue_depth, new_avg);
}
```

#### 2. Self-Tuning Scheduler Quantum

**Approach**: Adjust quantum based on context switch overhead.

```c
typedef struct adaptive_quantum {
    _Atomic uint64_t current_quantum_us;

    const uint64_t min_quantum_us;
    const uint64_t max_quantum_us;

    uint64_t last_throughput;
    uint64_t last_cs_rate;
} adaptive_quantum_t;

/* Tune quantum every 100ms */
void quantum_tune(adaptive_quantum_t *aq, adaptive_metrics_t *m)
{
    uint64_t cs_rate = atomic_load(&m->context_switch_rate);
    uint64_t throughput = atomic_load(&m->throughput);

    if (cs_rate > CONTEXT_SWITCH_THRESHOLD) {
        /* Too many context switches - increase quantum */
        uint64_t current = atomic_load(&aq->current_quantum_us);
        uint64_t new_quantum = MIN(current * 2, aq->max_quantum_us);
        atomic_store(&aq->current_quantum_us, new_quantum);
    } else if (throughput < aq->last_throughput * 0.95) {
        /* Throughput dropped - try decreasing quantum */
        uint64_t current = atomic_load(&aq->current_quantum_us);
        uint64_t new_quantum = MAX(current / 2, aq->min_quantum_us);
        atomic_store(&aq->current_quantum_us, new_quantum);
    }

    aq->last_throughput = throughput;
    aq->last_cs_rate = cs_rate;
}
```

#### 3. Adaptive Work-Stealing Strategy

**Approach**: Switch victim selection based on steal success rate and locality.

```c
typedef struct adaptive_ws_strategy {
    _Atomic ws_victim_strategy_t current;

    uint64_t random_success_rate;
    uint64_t circular_success_rate;
    uint64_t affinity_success_rate;

    uint64_t eval_interval_ticks;
    uint64_t last_eval_tick;
} adaptive_ws_strategy_t;

/* Evaluate and switch strategies */
void ws_strategy_adapt(adaptive_ws_strategy_t *aws, ws_stats_t *stats)
{
    /* Calculate success rates for each strategy */
    uint64_t success_rates[3] = {
        aws->random_success_rate,
        aws->circular_success_rate,
        aws->affinity_success_rate
    };

    /* Find best strategy */
    uint8_t best = 0;
    for (uint8_t i = 1; i < 3; i++) {
        if (success_rates[i] > success_rates[best]) {
            best = i;
        }
    }

    /* Switch if significantly better (5% threshold) */
    ws_victim_strategy_t current = atomic_load(&aws->current);
    if (success_rates[best] > success_rates[current] * 1.05) {
        atomic_store(&aws->current, (ws_victim_strategy_t)best);
    }
}
```

#### 4. Adaptive NUMA Allocation

**Approach**: Learn which nodes have fastest access for each CPU.

```c
typedef struct adaptive_numa {
    /* Learned access times (ns) */
    uint16_t access_times[MAX_CPUS][MAX_NUMA_NODES];

    /* Preferred node per CPU (cached) */
    _Atomic uint8_t preferred_node[MAX_CPUS];

    /* Update interval */
    uint64_t sample_interval_ticks;
} adaptive_numa_t;

/* Sample memory access latency */
void numa_sample_latency(adaptive_numa_t *an, uint8_t cpu, uint8_t node)
{
    /* Allocate on target node */
    void *ptr = numa_alloc(&topology, 4096, NUMA_ALLOC_SPECIFIC, node);

    /* Measure read latency */
    uint64_t start = rdtsc();
    volatile uint64_t *p = ptr;
    uint64_t val = *p;  /* Read to measure latency */
    uint64_t end = rdtsc();

    uint64_t cycles = end - start;
    an->access_times[cpu][node] = (uint16_t)(cycles / CPU_FREQ_GHZ);

    numa_free(&topology, ptr, 4096);
}

/* Update preferred node based on measurements */
void numa_update_preferred(adaptive_numa_t *an, uint8_t cpu)
{
    uint8_t fastest_node = 0;
    uint16_t min_time = an->access_times[cpu][0];

    for (uint8_t node = 1; node < topology.num_nodes; node++) {
        if (an->access_times[cpu][node] < min_time) {
            min_time = an->access_times[cpu][node];
            fastest_node = node;
        }
    }

    atomic_store(&an->preferred_node[cpu], fastest_node);
}
```

#### 5. Adaptive Cache Sizing

**Approach**: Tune cache size based on hit rate and memory pressure.

```c
typedef struct adaptive_cache {
    _Atomic uint32_t current_size;
    uint32_t min_size;
    uint32_t max_size;

    uint64_t target_hit_rate;  /* Per-mille (e.g., 900 = 90%) */
} adaptive_cache_t;

void cache_size_tune(adaptive_cache_t *ac, uint64_t hit_rate,
                     uint64_t memory_pressure)
{
    uint32_t current_size = atomic_load(&ac->current_size);

    if (hit_rate < ac->target_hit_rate && memory_pressure < 80) {
        /* Increase cache size */
        uint32_t new_size = MIN(current_size * 2, ac->max_size);
        atomic_store(&ac->current_size, new_size);
    } else if (hit_rate > ac->target_hit_rate * 1.05 || memory_pressure > 90) {
        /* Decrease cache size */
        uint32_t new_size = MAX(current_size / 2, ac->min_size);
        atomic_store(&ac->current_size, new_size);
    }
}
```

### Control Loop Architecture

```c
/* Main adaptive control loop (runs periodically) */
void adaptive_control_tick(pdac_system_t *sys)
{
    static uint64_t tick_counter = 0;
    tick_counter++;

    /* Update metrics (every tick) */
    for (uint8_t cpu = 0; cpu < sys->num_cpus; cpu++) {
        metrics_update(&sys->metrics, cpu);
    }

    /* Tune parameters (every 100 ticks) */
    if (tick_counter % 100 == 0) {
        quantum_tune(&sys->adaptive_quantum, &sys->metrics);
        ws_strategy_adapt(&sys->adaptive_ws, &sys->ws_stats);
    }

    /* NUMA sampling (every 1000 ticks) */
    if (tick_counter % 1000 == 0) {
        for (uint8_t cpu = 0; cpu < sys->num_cpus; cpu++) {
            numa_update_preferred(&sys->adaptive_numa, cpu);
        }
    }
}
```

### Expected Benefits

- **20-40% performance improvement** across diverse workloads
- **Automatic optimization** without manual tuning
- **Workload-adaptive**: Adjusts to changing conditions
- **Hardware-adaptive**: Learns NUMA topology, cache behavior

### Implementation Complexity

**Effort**: 3-4 weeks (600-900 lines + testing/validation)

**Risk**: Medium (need careful control theory, avoid oscillation)

**Files Affected**:
- New: `include/adaptive.h`, `kernel/adaptive.c`
- Modified: All scheduler/allocator files to read adaptive params

---

## Implementation Priority

1. **High Priority**: Task 5.5.1 (Lock-free capabilities) - highest impact, foundational
2. **High Priority**: Task 5.5.2 (RCU scheduler) - critical path optimization
3. **Medium Priority**: Task 5.5.3 (Algorithm optimization) - incremental gains
4. **Low Priority**: Task 5.5.4 (Self-tuning) - polish, requires other tasks first

## Testing Strategy

For each task:
1. **Unit tests**: Per-component correctness
2. **Integration tests**: System-wide behavior
3. **Performance tests**: Throughput, latency, scalability
4. **Stress tests**: Concurrency, memory pressure
5. **Regression tests**: Ensure no performance degradation

## Rollout Plan

**Phase 1** (Month 1-2): Task 5.5.1 (Capabilities)
- Implement lock-free hash table
- Migrate permission checks
- Validate correctness

**Phase 2** (Month 3-4): Task 5.5.2 (Scheduler)
- Convert ready queues to lock-free
- Migrate task state management
- Performance validation

**Phase 3** (Month 5-6): Tasks 5.5.3 + 5.5.4
- Profile and optimize hot paths
- Implement adaptive control
- System-wide benchmarking

---

## Conclusion

Phase 5.5 represents the final evolution of PDAC into a fully lock-free, RCU-protected, self-optimizing system. While the implementation effort is substantial (3-6 months total), the architectural patterns are well-established and the expected benefits are significant (5-10x performance improvement on highly concurrent workloads).

This document provides the roadmap for systematic implementation, with clear priorities, effort estimates, and expected outcomes. Each task builds on the Phase 5.1-5.4 foundation, creating a cohesive lock-free architecture throughout PDAC.

**Current Status**: Architecture complete, ready for implementation.

**Recommendation**: Implement incrementally (one task per month) with thorough testing between phases.
