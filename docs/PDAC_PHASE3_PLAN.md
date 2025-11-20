# PDAC Phase 3 Implementation Plan: Stochastic Scheduler Integration

**Date**: 2025-11-19
**Status**: Planning Complete - Ready for Implementation
**Duration Estimate**: ~30 hours
**Objective**: Integrate 8D resource vectors with stochastic hybrid scheduler

---

## Executive Summary

Phase 3 synthesizes the PDAC framework components (8D resource vectors, DAG scheduling, capability quotas) into a **provably fair, stochastically balanced, multidimensional scheduler**. This represents a novel contribution to OS scheduling theory.

**Key Innovation**: First scheduler to combine:
- Lottery scheduling (fairness)
- Beatty sequences (deterministic irrational spacing)
- Octonion-based resource weighting (multidimensional optimization)
- Token bucket admission control (QoS guarantees)

---

## Background: Why This Scheduler Design?

### The Scheduling Trilemma

Traditional schedulers face a trilemma:

1. **Fairness** (CFS, lottery): Fair but not optimal
2. **Performance** (O(1), deadline): Fast but can starve tasks
3. **Multidimensional** (Borg, Kubernetes): Complex but practical

**PDAC Solution**: Hybrid approach that achieves all three:
- **Fairness**: Lottery scheduling ensures proportional CPU time
- **Performance**: Beatty sequences provide deterministic spacing (no clustering)
- **Multidimensional**: Octonion norm maps 8D resources to scalar priority

### Real-World Inspiration

| System | Scheduler Type | Strengths | Weaknesses |
|--------|---------------|-----------|------------|
| **Linux CFS** | Completely Fair Scheduler | Fair, O(log n) | Single-dimensional (vruntime) |
| **Lottery (Waldspurger)** | Probabilistic | Provably fair | Can be bursty |
| **Google Borg** | Priority + quota | Multidimensional | Complex, proprietary |
| **Kubernetes** | Priority + preemption | Good for containers | No formal fairness |
| **PDAC (ours)** | Hybrid lottery+Beatty | Fair + multidimensional | Novel (unproven at scale) |

---

## Phase 3 Architecture

```
┌─────────────────────────────────────────────────────────┐
│                  SCHEDULER CORE                          │
│  ┌───────────────────────────────────────────────────┐  │
│  │  Hybrid Scheduler (80% lottery, 20% Beatty)       │  │
│  │  - Mode selection (LCG random choice)             │  │
│  │  - Task selection from ready queue                │  │
│  │  - Context switch logic                           │  │
│  └───────────┬───────────────────────┬─────────────────┘  │
│              │                       │                    │
│     ┌────────▼────────┐     ┌────────▼─────────┐        │
│     │ Lottery Scheduler│     │ Beatty Scheduler │        │
│     │ - Weighted tickets│    │ - Irrational gaps│        │
│     │ - LCG random pick│     │ - Deterministic  │        │
│     └────────┬────────┘     └────────┬─────────┘        │
│              │                       │                    │
│              └───────────┬───────────┘                    │
│                          │                                │
│              ┌───────────▼───────────┐                    │
│              │  Priority Computation │                    │
│              │  - Octonion norm      │                    │
│              │  - 8D → scalar        │                    │
│              └───────────┬───────────┘                    │
└──────────────────────────┼─────────────────────────────────┘
                           │
            ┌──────────────▼──────────────┐
            │  Admission Control          │
            │  - Token bucket check       │
            │  - Resource availability    │
            │  - Stochastic accept/reject │
            └──────────────┬──────────────┘
                           │
            ┌──────────────▼──────────────┐
            │  Ready Queue (DAG-aware)    │
            │  - Tasks with deps satisfied│
            │  - Sorted by priority       │
            └─────────────────────────────┘
```

---

## Task Breakdown

### Task 3.1: Linear Congruential Generator (LCG)

**File**: `kernel/lcg.c` (120 lines)
**Time**: 2 hours

**Purpose**: Provide deterministic pseudo-random numbers for lottery scheduling and stochastic admission control.

**Algorithm**: Classic LCG formula
```
X[n+1] = (a * X[n] + c) mod m
```

**Parameters** (from Numerical Recipes):
- `a = 1664525` (multiplier)
- `c = 1013904223` (increment)
- `m = 2^32` (modulus, implicit in uint32_t)
- Period: ~4 billion (sufficient for scheduler)

**API**:
```c
void lcg_init(lcg_state_t *state, uint32_t seed);
uint32_t lcg_next(lcg_state_t *state);               // Returns [0, 2^32-1]
uint32_t lcg_range(lcg_state_t *state, uint32_t max); // Returns [0, max-1]
double lcg_uniform(lcg_state_t *state);               // Returns [0.0, 1.0)
```

**Success Criteria**:
- Statistical tests pass (chi-squared, runs test)
- Period verified empirically
- Thread-safe (per-CPU state)

---

### Task 3.2: Lottery Scheduling

**File**: `kernel/sched_lottery.c` (250 lines)
**Time**: 4 hours

**Purpose**: Implement Waldspurger's lottery scheduling with resource-weighted tickets.

**Core Idea**:
- Each task gets tickets proportional to resource priority
- Random number selects "winning" ticket
- Winner runs next

**Ticket Calculation**:
```c
tickets = octonion_norm(task->resources) * BASE_TICKETS
```

Where `octonion_norm()` computes:
```
norm = sqrt(cpu² + mem² + io² + net² + gpu² + disk² + irq² + cap²)
```

**Algorithm**:
1. Sum all tickets in ready queue
2. Generate random number in [0, total_tickets)
3. Walk queue subtracting tickets until random exhausted
4. Winner is current task

**Example**:
```
Task A: 100 tickets
Task B: 200 tickets
Task C: 50 tickets
Total: 350 tickets

Random = 175
175 - 100 = 75  (skip A)
75 - 200 < 0    (select B!)
```

**API**:
```c
void lottery_init(lottery_scheduler_t *sched, lcg_state_t *rng);
dag_task_t *lottery_select(lottery_scheduler_t *sched, dag_pdac_t *dag);
void lottery_update_tickets(dag_task_t *task, resource_vector_t resources);
```

**Real-World**: Similar to VMware ESXi shares-based scheduling.

---

### Task 3.3: Beatty Sequence Scheduler

**File**: `kernel/sched_beatty.c` (180 lines)
**Time**: 3 hours

**Purpose**: Implement deterministic scheduling using irrational number sequences.

**Mathematical Background**:
Beatty sequence for irrational α:
```
B_α(n) = floor(n * α)
```

Using **golden ratio** φ = (1 + √5) / 2 ≈ 1.618:
```
B_φ(1) = 1
B_φ(2) = 3
B_φ(3) = 4
B_φ(4) = 6
B_φ(5) = 8
...
```

**Key Property**: Gaps between consecutive elements are deterministically distributed (never cluster).

**Scheduling Application**:
- Sort tasks by priority (octonion norm)
- Select task at position B_φ(counter) mod num_ready_tasks
- Increment counter

**Advantages**:
- Deterministic (repeatable)
- No clustering (even distribution)
- Low-priority tasks never starve

**Implementation** (Q16.16 fixed-point):
```c
#define GOLDEN_RATIO Q16(1.618033988749895)

uint32_t beatty_next(beatty_state_t *state) {
    state->counter++;
    return (state->counter * GOLDEN_RATIO) >> 16; // Q16.16 multiplication
}
```

**API**:
```c
void beatty_init(beatty_state_t *state);
dag_task_t *beatty_select(beatty_state_t *state, dag_pdac_t *dag);
```

**Pedagogical Note**: Demonstrates how pure math (irrational numbers) solves practical problems (task distribution).

---

### Task 3.4: Hybrid Lottery + Beatty Scheduler

**File**: `kernel/sched_hybrid.c` (200 lines)
**Time**: 4 hours

**Purpose**: Combine lottery (fairness) and Beatty (determinism) for best of both worlds.

**Algorithm**:
```c
if (lcg_uniform(rng) < 0.8) {
    // 80% probability: Use lottery (fairness)
    task = lottery_select(&lottery, dag);
} else {
    // 20% probability: Use Beatty (determinism)
    task = beatty_select(&beatty, dag);
}
```

**Why 80/20 Split?**
- **80% lottery**: Ensures fairness guarantees hold
- **20% Beatty**: Prevents starvation, reduces variance

**Provable Properties**:
1. **Fairness**: Expected CPU time ~ ticket proportion (80% + 20% fallback)
2. **Starvation-Free**: Beatty ensures all tasks run eventually
3. **Bounded Wait**: Max wait = O(num_tasks * time_quantum)

**API**:
```c
void hybrid_init(hybrid_scheduler_t *sched, lcg_state_t *rng);
dag_task_t *hybrid_select(hybrid_scheduler_t *sched, dag_pdac_t *dag);
void hybrid_update_mode(hybrid_scheduler_t *sched); // Switch lottery/Beatty
```

**Benchmarking**: Compare against Linux CFS on fairness metrics.

---

### Task 3.5: Stochastic Admission Control

**File**: `kernel/sched_admission.c` (150 lines)
**Time**: 3 hours

**Purpose**: Prevent system overload using probabilistic admission with token buckets.

**Problem**: DAG can have more runnable tasks than system resources.

**Solution**: Stochastic admission:
1. Task becomes ready → check token bucket
2. If tokens available → admit (100%)
3. If tokens exhausted → probabilistic admit based on load

**Algorithm**:
```c
bool admit_task(admission_control_t *ac, dag_task_t *task) {
    // Check hard quota (token bucket)
    if (token_bucket_consume(&ac->quota, task->resources.norm)) {
        return true; // Under quota, always admit
    }

    // Over quota: probabilistic admission
    double load = compute_system_load(ac->dag);
    double admit_prob = 1.0 / (1.0 + load); // P = 1 / (1 + load)

    return lcg_uniform(ac->rng) < admit_prob;
}
```

**Load Computation** (8D):
```c
double compute_system_load(dag_pdac_t *dag) {
    resource_vector_t used = sum_running_tasks(dag);
    return vector_norm(used) / vector_norm(dag->system_quota);
}
```

**Properties**:
- **Light load** (load < 1): Admit probability ~50%+
- **Heavy load** (load >> 1): Admit probability ~0%
- **Graceful degradation**: No hard cutoff

**Integration with Token Buckets** (from Phase 2.4):
- Each task has capability with token bucket
- Scheduler consumes tokens on admission
- Tokens refill over time

**API**:
```c
void admission_init(admission_control_t *ac, lcg_state_t *rng);
bool admission_try_admit(admission_control_t *ac, dag_task_t *task);
double admission_get_load(admission_control_t *ac);
```

---

### Task 3.6: Scheduler Testing & Benchmarks

**File**: `kernel/test_scheduler.c` (400 lines)
**Time**: 6 hours

**Test Categories**:

**1. Unit Tests** (15 tests):
- LCG statistical properties
- Lottery fairness (chi-squared test)
- Beatty distribution (gap analysis)
- Hybrid mode switching
- Admission control under load

**2. Integration Tests** (10 tests):
- DAG with dependencies (topological order preserved)
- Resource quota enforcement
- Capability integration (token buckets)
- Starvation prevention
- Deadlock detection

**3. Benchmarks**:
- **Fairness**: Compare ticket proportions vs. actual CPU time
- **Latency**: Measure scheduling decision time (μs)
- **Throughput**: Tasks completed per second
- **Overhead**: Scheduler CPU usage (%)

**Benchmark Workloads**:
```c
// Workload 1: CPU-bound (equal priorities)
for (i = 0; i < 10; i++) {
    add_task(dag, CPU_intensive, priority=100);
}

// Workload 2: Mixed (varied priorities)
add_task(dag, high_priority, tickets=500);
add_task(dag, medium_priority, tickets=200);
add_task(dag, low_priority, tickets=50);

// Workload 3: Bursty (admission control test)
for (i = 0; i < 100; i++) {
    add_task(dag, short_burst, priority=100);
}
```

**Success Criteria**:
- Fairness: CPU time within 5% of ticket proportion
- Latency: < 10 μs per scheduling decision
- Throughput: > 10,000 tasks/sec
- Overhead: < 5% CPU usage

---

### Task 3.7: Documentation

**File**: `docs/SCHEDULER_ARCHITECTURE.md` (500 lines)
**Time**: 4 hours

**Sections**:
1. **Overview**: Hybrid lottery+Beatty design
2. **Mathematical Background**: Octonion norms, Beatty sequences
3. **API Reference**: All scheduler functions
4. **Usage Guide**: How to configure and tune
5. **Performance Analysis**: Benchmark results
6. **Comparison Table**: vs. Linux CFS, VMware, Borg
7. **Future Work**: RCU integration, NUMA awareness

---

## Implementation Schedule

| Week | Tasks | Hours | Deliverables |
|------|-------|-------|--------------|
| 1 | LCG + Lottery | 6h | LCG + lottery scheduler |
| 2 | Beatty + Hybrid | 7h | Complete hybrid scheduler |
| 3 | Admission + Integration | 7h | Full system integration |
| 4 | Testing + Docs | 10h | Tests, benchmarks, docs |
| **Total** | **All tasks** | **30h** | **Production scheduler** |

---

## Success Metrics

| Metric | Target | Measurement |
|--------|--------|-------------|
| **Fairness** | CPU time within 5% of proportional share | Chi-squared test |
| **Latency** | < 10 μs per decision | Cycle counter |
| **Throughput** | > 10k tasks/sec | Benchmark |
| **Starvation** | All tasks run within 100ms | Max wait time |
| **Correctness** | All unit tests pass | 25+ tests |

---

## Novel Contributions

1. **First scheduler using octonion algebra** for multidimensional resource weighting
2. **Hybrid lottery+Beatty** combining probabilistic fairness with deterministic spacing
3. **8D admission control** with stochastic backpressure
4. **Formal fairness proofs** using probabilistic analysis
5. **Integration with capability system** for end-to-end resource management

---

## Dependencies

**Phase 1** (✅ Complete):
- `resource_vector.h` - 8D resource vectors
- `dag_pdac.h` - DAG structure and operations

**Phase 2** (✅ Complete):
- `token_bucket.c` - Rate limiting for admission control
- `capability_v2.c` - Resource quotas per task

**New Components** (Phase 3):
- LCG random number generator
- Lottery scheduler
- Beatty scheduler
- Hybrid mode selector
- Admission controller

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| LCG period too short | Low | Medium | Use 64-bit LCG if needed |
| Lottery unfair at small scales | Medium | Low | Add minimum time quantum |
| Beatty clustering at boundaries | Low | Low | Use φ (proven non-clustering) |
| Admission too conservative | Medium | Medium | Tune admit probability curve |
| Integration bugs | High | High | Comprehensive unit tests |

---

## Future Enhancements (Phase 4+)

- [ ] Multi-core support (per-CPU run queues)
- [ ] NUMA-aware scheduling (locality optimization)
- [ ] Real-time guarantees (EDF integration)
- [ ] Power management (DVFS integration)
- [ ] Machine learning (adaptive 80/20 split)

---

**Status**: ✅ Planning Complete
**Next Step**: Begin Task 3.1 (LCG Implementation)
**Estimated Completion**: 4 weeks (30 hours)
