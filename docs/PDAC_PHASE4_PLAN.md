# PDAC Phase 4 Implementation Plan: Execution Framework & Multi-Core Integration

**Date**: 2025-11-19
**Status**: Planning Complete - Ready for Implementation
**Duration Estimate**: ~24 hours
**Objective**: Bridge scheduling theory to practice with complete execution framework

---

## Executive Summary

Phase 4 transforms the PDAC scheduler from a theoretical artifact into a **production-ready execution framework**. While Phase 3 answered "which task to run?", Phase 4 answers "how do we actually run it?"

**Key Innovation**: First pedagogical OS to combine:
- Octonion-based multidimensional scheduling (Phase 3)
- Capability-based security (Phase 2)
- Multi-core execution with per-CPU run queues
- Real-time performance telemetry
- Complete DAG execution engine

---

## Background: From Scheduling to Execution

### The Execution Problem

A scheduler alone is insufficient for a real OS:

```
Scheduler: "Task A should run next"
   ↓
   ??? (How do we actually execute it?)
   ↓
Execution: [Task A running with correct resources, time quantum, context]
```

**Missing Pieces**:
1. **Task execution model**: What does it mean to "run" a task?
2. **Context switching**: How do we switch between tasks?
3. **Time quantum**: When do we preempt a running task?
4. **Multi-core**: How do we schedule across multiple CPUs?
5. **Performance monitoring**: Is the scheduler working correctly?
6. **DAG execution**: How do we run dependency graphs?

### Real-World Inspiration

| System | Execution Model | Multi-Core Strategy | Monitoring |
|--------|----------------|---------------------|------------|
| **Linux** | Process context + preemption | Per-CPU run queues + load balancing | perf, ftrace |
| **FreeBSD** | Thread-based ULE scheduler | CPU affinity + migration | DTrace |
| **Xen** | Virtual CPU scheduling | Credit scheduler per-PCPU | xenmon |
| **PDAC (ours)** | Capability-bounded execution | Hybrid scheduler per-CPU | Integrated telemetry |

---

## Phase 4 Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    USER WORKLOAD                             │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐            │
│  │  DAG Task  │  │  DAG Task  │  │  DAG Task  │            │
│  │     A      │→ │     B      │→ │     C      │            │
│  └────────────┘  └────────────┘  └────────────┘            │
└────────────────────────┬─────────────────────────────────────┘
                         │
         ┌───────────────▼────────────────┐
         │   DAG EXECUTION ENGINE         │
         │   - Topological order          │
         │   - Dependency tracking        │
         │   - Task state machine         │
         └───────────────┬────────────────┘
                         │
         ┌───────────────▼────────────────┐
         │   MULTI-CORE DISPATCHER        │
         │   - CPU assignment             │
         │   - Load balancing             │
         │   - Affinity hints             │
         └───────────────┬────────────────┘
                         │
         ┌───────────────┴────────────────┐
         │                                 │
    ┌────▼─────┐  ┌────▼─────┐  ┌────▼─────┐
    │  CPU 0   │  │  CPU 1   │  │  CPU 2   │
    │ ┌──────┐ │  │ ┌──────┐ │  │ ┌──────┐ │
    │ │Hybrid│ │  │ │Hybrid│ │  │ │Hybrid│ │
    │ │Sched │ │  │ │Sched │ │  │ │Sched │ │
    │ └──┬───┘ │  │ └──┬───┘ │  │ └──┬───┘ │
    │    │     │  │    │     │  │    │     │
    │ ┌──▼───┐ │  │ ┌──▼───┐ │  │ ┌──▼───┐ │
    │ │ Run  │ │  │ │ Run  │ │  │ │ Run  │ │
    │ │Queue │ │  │ │Queue │ │  │ │Queue │ │
    │ └──┬───┘ │  │ └──┬───┘ │  │ └──┬───┘ │
    │    │     │  │    │     │  │    │     │
    │ ┌──▼───┐ │  │ ┌──▼───┐ │  │ ┌──▼───┐ │
    │ │Task  │ │  │ │Task  │ │  │ │Task  │ │
    │ │Exec  │ │  │ │Exec  │ │  │ │Exec  │ │
    │ └──────┘ │  │ └──────┘ │  │ └──────┘ │
    └────┬─────┘  └────┬─────┘  └────┬─────┘
         │             │             │
         └─────────────┴─────────────┘
                       │
         ┌─────────────▼─────────────┐
         │   TELEMETRY & MONITORING   │
         │   - Task latency           │
         │   - CPU utilization        │
         │   - Scheduler fairness     │
         │   - Resource consumption   │
         └────────────────────────────┘
```

---

## Task Breakdown

### Task 4.1: Task Execution Model

**Files**: `kernel/task_exec.c` (300 lines), `include/task_exec.h` (150 lines)
**Time**: 4 hours

**Purpose**: Define what it means to execute a task in PDAC.

**Task Execution Lifecycle**:
```
NEW → ADMITTED → READY → RUNNING → [BLOCKED/READY] → COMPLETED
```

**Task Context**:
```c
typedef struct task_context {
    /* Execution state */
    uint64_t start_time;        // When task started running
    uint64_t cpu_time_used;     // Total CPU time consumed
    uint64_t quantum_remaining; // Time left in current quantum

    /* Capability */
    int capability_slot;        // Capability for resource access

    /* CPU affinity */
    uint8_t cpu_id;            // Which CPU is executing this
    uint8_t preferred_cpu;     // Hint for scheduler

    /* Performance counters */
    uint64_t context_switches;  // Times preempted
    uint64_t cache_misses;      // Simulated cache behavior
} task_context_t;
```

**Time Quantum Management**:
```c
#define TIME_QUANTUM_MS 10  // 10ms default quantum

// Check if task should be preempted
bool task_should_preempt(task_context_t *ctx, uint64_t now);

// Consume quantum time
void task_consume_quantum(task_context_t *ctx, uint64_t elapsed);

// Reset quantum (after preemption)
void task_reset_quantum(task_context_t *ctx);
```

**Context Switch Simulation**:
```c
// Simulate context switch overhead (cache flush, TLB flush, etc.)
void task_context_switch(task_context_t *from, task_context_t *to);

// Estimated cost: ~1-5 microseconds (configurable)
#define CONTEXT_SWITCH_COST_US 2
```

**API**:
```c
void task_exec_init(task_context_t *ctx, dag_task_t *task, int cap_slot);
void task_exec_start(task_context_t *ctx, uint64_t now);
void task_exec_run(task_context_t *ctx, uint64_t duration_ms);
void task_exec_preempt(task_context_t *ctx, uint64_t now);
void task_exec_complete(task_context_t *ctx, uint64_t now);
```

**Success Criteria**:
- Task lifecycle state machine works correctly
- Quantum management enforces time limits
- Context switch overhead is accounted for

---

### Task 4.2: Per-CPU Run Queues

**Files**: `kernel/percpu_sched.c` (400 lines), `include/percpu_sched.h` (200 lines)
**Time**: 5 hours

**Purpose**: Enable true multi-core scheduling with per-CPU state.

**Per-CPU Scheduler**:
```c
typedef struct percpu_scheduler {
    uint8_t cpu_id;                    // CPU identifier

    /* Hybrid scheduler (from Phase 3) */
    hybrid_scheduler_t sched;          // Per-CPU scheduler instance

    /* Run queue */
    dag_task_t *ready_queue[64];       // Ready tasks for this CPU
    uint16_t num_ready;                // Count of ready tasks

    /* Currently running */
    dag_task_t *current_task;          // Task executing on this CPU
    task_context_t *current_context;   // Execution context

    /* Statistics */
    uint64_t total_tasks_run;          // Tasks executed
    uint64_t total_idle_time;          // CPU idle cycles
    uint64_t total_busy_time;          // CPU busy cycles
} percpu_scheduler_t;
```

**Multi-Core Dispatcher**:
```c
typedef struct multicore_dispatcher {
    percpu_scheduler_t cpus[MAX_CPUS]; // Per-CPU schedulers
    uint8_t num_cpus;                   // Number of CPUs

    /* Global DAG */
    dag_pdac_t *dag;                    // Shared task graph

    /* Load balancing */
    uint64_t last_balance_time;         // Last load balance
    uint32_t balance_interval_ms;       // Balance every N ms
} multicore_dispatcher_t;
```

**Task Assignment Strategy**:
```c
// Assign task to CPU with lowest load
uint8_t assign_task_to_cpu(multicore_dispatcher_t *dispatch, dag_task_t *task);

// Compute CPU load (running + ready tasks)
double compute_cpu_load(percpu_scheduler_t *cpu);

// Migrate task from one CPU to another (if beneficial)
void migrate_task(multicore_dispatcher_t *dispatch,
                  dag_task_t *task,
                  uint8_t from_cpu,
                  uint8_t to_cpu);
```

**Load Balancing Algorithm**:
```
Every 100ms:
1. Compute load for each CPU
2. If max_load - min_load > THRESHOLD (e.g., 2.0):
   - Find overloaded CPU
   - Find underloaded CPU
   - Migrate one task from overloaded to underloaded
```

**API**:
```c
void percpu_sched_init(percpu_scheduler_t *cpu, uint8_t cpu_id, lcg_state_t *rng);
void percpu_sched_add_task(percpu_scheduler_t *cpu, dag_task_t *task);
dag_task_t *percpu_sched_select_next(percpu_scheduler_t *cpu);
void multicore_dispatch_init(multicore_dispatcher_t *dispatch, uint8_t num_cpus);
void multicore_dispatch_balance(multicore_dispatcher_t *dispatch);
```

**Real-World Parallel**: Similar to Linux CFS per-CPU run queues, but with hybrid lottery+Beatty selection.

---

### Task 4.3: Performance Telemetry

**Files**: `kernel/sched_telemetry.c` (350 lines), `include/sched_telemetry.h` (150 lines)
**Time**: 4 hours

**Purpose**: Real-time monitoring and performance analysis.

**Telemetry Metrics**:
```c
typedef struct sched_telemetry {
    /* Per-task metrics */
    struct {
        uint64_t wait_time_us;      // Time spent waiting (READY)
        uint64_t run_time_us;       // Time spent running
        uint64_t turnaround_time_us; // NEW → COMPLETED
        uint32_t preemptions;       // Times preempted
    } tasks[DAG_MAX_TASKS];

    /* Per-CPU metrics */
    struct {
        double utilization;         // % time busy
        uint64_t tasks_executed;    // Total tasks run
        uint64_t context_switches;  // Total context switches
    } cpus[MAX_CPUS];

    /* Global metrics */
    uint64_t total_throughput;      // Tasks completed / second
    double avg_latency_ms;          // Average turnaround time
    double scheduler_overhead_pct;  // % time in scheduler

    /* Fairness tracking */
    double fairness_index;          // Jain's fairness index
} sched_telemetry_t;
```

**Jain's Fairness Index**:
```
FI = (Σ x_i)² / (n × Σ x_i²)

Where x_i = CPU time for task i
FI = 1.0 → perfect fairness
FI < 0.8 → poor fairness
```

**Real-Time Dashboard**:
```c
void telemetry_print_dashboard(sched_telemetry_t *telem);

// Output example:
// ╔═══════════════════════════════════════╗
// ║  PDAC SCHEDULER TELEMETRY             ║
// ╠═══════════════════════════════════════╣
// ║  Throughput: 15,234 tasks/sec         ║
// ║  Avg Latency: 12.3 ms                 ║
// ║  Fairness Index: 0.96                 ║
// ║  CPU Utilization: 87.2%               ║
// ╚═══════════════════════════════════════╝
```

**Histogram Support**:
```c
// Latency histogram (log scale)
void telemetry_compute_latency_histogram(sched_telemetry_t *telem,
                                         uint32_t *buckets,
                                         uint32_t num_buckets);
```

**API**:
```c
void telemetry_init(sched_telemetry_t *telem);
void telemetry_record_task_start(sched_telemetry_t *telem, uint16_t task_id);
void telemetry_record_task_complete(sched_telemetry_t *telem, uint16_t task_id);
void telemetry_record_context_switch(sched_telemetry_t *telem, uint8_t cpu_id);
void telemetry_update(sched_telemetry_t *telem, uint64_t now);
double telemetry_compute_fairness(sched_telemetry_t *telem, dag_pdac_t *dag);
```

---

### Task 4.4: DAG Execution Engine

**Files**: `kernel/dag_executor.c` (450 lines), `include/dag_executor.h` (200 lines)
**Time**: 6 hours

**Purpose**: Execute entire DAG graphs with dependency tracking.

**DAG Executor**:
```c
typedef struct dag_executor {
    /* DAG and scheduling */
    dag_pdac_t *dag;
    multicore_dispatcher_t *dispatcher;
    admission_control_t *admission;

    /* Execution state */
    uint64_t start_time;
    uint64_t end_time;
    bool running;

    /* Telemetry */
    sched_telemetry_t telemetry;
} dag_executor_t;
```

**Execution Algorithm**:
```
1. Topological sort (validate no cycles)
2. For each task in topological order:
   a. Wait for dependencies to complete
   b. Try admission control
   c. Assign to CPU
   d. Add to ready queue
3. Per-CPU loop:
   a. Select next task (hybrid scheduler)
   b. Execute for quantum
   c. Update dependencies
   d. Repeat until DAG complete
```

**Dependency Resolution**:
```c
// Check if all dependencies are satisfied
bool dag_executor_deps_satisfied(dag_executor_t *exec, dag_task_t *task);

// Mark task as ready (dependencies complete)
void dag_executor_mark_ready(dag_executor_t *exec, dag_task_t *task);

// Update dependents after task completes
void dag_executor_update_dependents(dag_executor_t *exec, dag_task_t *task);
```

**Execution Modes**:
```c
// Synchronous: Execute DAG to completion
void dag_executor_run_sync(dag_executor_t *exec);

// Asynchronous: Single step
bool dag_executor_step(dag_executor_t *exec);

// Simulation: Run with virtual time
void dag_executor_simulate(dag_executor_t *exec, uint64_t duration_ms);
```

**API**:
```c
void dag_executor_init(dag_executor_t *exec,
                       dag_pdac_t *dag,
                       uint8_t num_cpus);
void dag_executor_start(dag_executor_t *exec);
void dag_executor_run_sync(dag_executor_t *exec);
bool dag_executor_is_complete(dag_executor_t *exec);
void dag_executor_print_stats(dag_executor_t *exec);
```

---

### Task 4.5: Complete End-to-End Examples

**Files**: `kernel/examples_phase4.c` (500 lines)
**Time**: 3 hours

**Example Categories**:

1. **Simple Pipeline** (A → B → C)
2. **Diamond DAG** (A → [B, C] → D)
3. **Parallel Workload** (10 independent tasks)
4. **Mixed Priority** (high, medium, low priority tasks)
5. **Overload Scenario** (admission control stress test)
6. **Multi-Core Scaling** (1 CPU vs. 4 CPUs)

**Example Template**:
```c
void example_simple_pipeline(void) {
    printf("\n=== Example: Simple Pipeline (A → B → C) ===\n");

    // Setup DAG
    dag_pdac_t dag;
    pdac_dag_init(&dag, system_quota);

    int a = pdac_dag_add_task(&dag, "Task A", res_a);
    int b = pdac_dag_add_task(&dag, "Task B", res_b);
    int c = pdac_dag_add_task(&dag, "Task C", res_c);

    pdac_dag_add_dependency(&dag, b, a);
    pdac_dag_add_dependency(&dag, c, b);

    // Execute
    dag_executor_t exec;
    dag_executor_init(&exec, &dag, 2); // 2 CPUs
    dag_executor_run_sync(&exec);

    // Print results
    dag_executor_print_stats(&exec);
    telemetry_print_dashboard(&exec.telemetry);
}
```

---

### Task 4.6: Execution Framework Tests

**Files**: `kernel/test_execution.c` (600 lines)
**Time**: 5 hours

**Test Categories**:

1. **Task Execution Tests** (8 tests)
   - Lifecycle state machine
   - Quantum management
   - Context switch accounting
   - Preemption logic

2. **Per-CPU Tests** (6 tests)
   - Task assignment
   - Load balancing
   - CPU affinity
   - Migration logic

3. **Telemetry Tests** (5 tests)
   - Metric recording
   - Fairness computation
   - Histogram generation
   - Dashboard output

4. **DAG Executor Tests** (7 tests)
   - Simple pipeline execution
   - Diamond DAG
   - Dependency resolution
   - Parallel execution
   - Admission integration
   - Multi-core scaling
   - Completion detection

**Total**: 26 tests

---

### Task 4.7: Execution Architecture Documentation

**Files**: `docs/EXECUTION_ARCHITECTURE.md` (800 lines)
**Time**: 3 hours

**Sections**:
1. Overview (execution model, multi-core strategy)
2. Task lifecycle and state machine
3. Per-CPU scheduling architecture
4. Load balancing algorithms
5. Performance telemetry guide
6. DAG execution patterns
7. API reference and examples
8. Performance tuning guide
9. Comparison with Linux, FreeBSD, Xen
10. Future work (NUMA, real-time, power)

---

## Implementation Schedule

| Week | Tasks | Hours | Deliverables |
|------|-------|-------|--------------|
| 1 | Task execution + per-CPU | 9h | Execution model + multi-core |
| 2 | Telemetry + DAG executor | 10h | Monitoring + execution engine |
| 3 | Examples + tests | 8h | 6 examples + 26 tests |
| 4 | Documentation | 3h | Complete architecture guide |
| **Total** | **All tasks** | **30h** | **Production execution framework** |

---

## Success Metrics

| Metric | Target | Measurement |
|--------|--------|-------------|
| **Multi-core speedup** | 3.5x on 4 CPUs | DAG completion time |
| **Load balance** | Utilization within 10% across CPUs | Per-CPU telemetry |
| **Overhead** | Scheduler < 5% of total time | Telemetry profiling |
| **Fairness** | Jain's index > 0.90 | Telemetry computation |
| **Latency** | P99 < 50ms for small tasks | Histogram analysis |

---

## Novel Contributions

1. **Integrated execution framework** for octonion-based scheduler
2. **Capability-bounded task execution** (security + resource control)
3. **Real-time fairness monitoring** (Jain's index computation)
4. **DAG execution with hybrid scheduling** across multiple CPUs
5. **Pedagogical multi-core scheduler** (simpler than Linux but feature-complete)

---

## Dependencies

**Phase 3** (✅ Complete):
- Hybrid scheduler (lottery + Beatty)
- Admission control
- LCG random number generator

**Phase 2** (✅ Complete):
- Capability system (for task access control)
- Token buckets (used in admission)

**Phase 1** (✅ Complete):
- DAG structure
- Resource vectors

**New Components** (Phase 4):
- Task execution model
- Per-CPU run queues
- Performance telemetry
- DAG executor
- End-to-end examples

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Simulation vs. real execution gap | Medium | Low | Document assumptions clearly |
| Load balancing too complex | Low | Medium | Start with simple threshold-based |
| Telemetry overhead | Low | Low | Use sampling, not per-event |
| DAG executor edge cases | Medium | Medium | Comprehensive tests (26 tests) |
| Multi-core race conditions | Low | High | Use per-CPU state (no sharing) |

---

## Future Enhancements (Phase 5+)

- [ ] NUMA-aware scheduling (locality optimization)
- [ ] Real-time scheduling (EDF, RMS integration)
- [ ] Priority inheritance (solve priority inversion)
- [ ] Work stealing (more aggressive load balancing)
- [ ] Power management (DVFS integration)
- [ ] Container isolation (cgroups-like resource limits)

---

**Status**: ✅ Planning Complete
**Next Step**: Begin Task 4.1 (Task Execution Model)
**Estimated Completion**: 4 weeks (30 hours)
