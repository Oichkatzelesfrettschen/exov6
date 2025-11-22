# Beatty Sequence Scheduler Specification

## Overview

The Beatty Scheduler is a deterministic, quasi-random scheduler based on the mathematical properties of Beatty sequences. It utilizes the golden ratio $\varphi$ to produce a schedule that is both deterministic and evenly distributed, avoiding the clustering issues of random scheduling while providing better fairness properties than strict round-robin.

## Mathematical Specification

### Beatty Sequence

A Beatty sequence for an irrational number $\alpha$ is defined as:

$$ B_\alpha(n) = \lfloor n \times \alpha \rfloor $$

For this scheduler, we use the golden ratio $\varphi \approx 1.618$:

$$ \alpha = \varphi = \frac{1 + \sqrt{5}}{2} $$

### Selection Formula

Given a counter $C$ (monotonically increasing) and a list of $N$ ready tasks sorted by priority:

1.  Compute the Beatty number: $B = \lfloor C \times \varphi \rfloor$
2.  Select the task at index: $I = B \mod N$

Since $N$ can vary as tasks block or wake up, the selection index effectively samples the priority-sorted list in a quasi-uniform distribution that respects the non-periodic nature of the golden ratio.

### Invariants

1.  **Determinism**: Given the same sequence of task arrivals and blocking behavior, the schedule is identical.
2.  **Starvation Freedom**: The sequence $B \mod N$ covers all indices $0 \dots N-1$ eventually.
3.  **Three-Distance Property**: The gaps between consecutive selections of the same index are limited to at most 3 distinct values, preventing bursty clustering.

## Algorithm

### Data Structures

*   **Ready Queue**: A list of tasks currently in `TASK_STATE_READY`.
*   **Counter**: A global (or per-core) monotonic counter $C$.
*   **Sorted Order**: The ready queue is maintained sorted by priority (resource norm).

### Selection Logic (Pseudo-code)

```c
function beatty_select(ready_queue):
    N = length(ready_queue)
    if N == 0: return NULL

    // 1. Sort ready queue by priority (descending)
    // Note: In O(1) implementation, this is maintained incrementally
    sort(ready_queue)

    // 2. Compute index
    B = floor(counter * PHI)
    index = B % N

    // 3. Select task
    task = ready_queue[index]

    // 4. Advance counter
    counter += 1

    return task
```

### Complexity

*   **Selection**: $O(1)$ arithmetic operations.
*   **Maintenance**: $O(N \log N)$ if sorting every time. To achieve $O(1)$ selection overhead, the ready queue must be maintained as a sorted structure (e.g., valid/invalid bitmasks over a fixed priority set, or incrementally sorted). The current implementation performs a sort on selection, which is $O(N^2)$ worst case for insertion sort or $O(N \log N)$ for quicksort.

## Interactions and Risks

### Multi-Core Interaction

*   **Per-Core Sequences**: To avoid global lock contention and cache line bouncing, each core maintains its own `beatty_scheduler_t` instance and counter.
*   **Global Load Balancing**: A separate work-stealing mechanism (or periodic rebalancing) moves tasks between per-core queues. The Beatty logic applies only to the local run queue.
*   **Shared Global Sequence**: Not recommended due to synchronization overhead.

### Priorities

*   **Sorting**: Tasks are sorted by priority.
*   **Mixing**: The Beatty index selects a position in the sorted list. Index 0 is highest priority, Index $N-1$ is lowest.
*   **Distribution**: Since $B \mod N$ is roughly uniform, high and low priority tasks are selected with equal *frequency* over time, but the *ordering* is deterministic.
    *   *Risk*: This effectively negates priority for throughput (everyone gets $1/N$ share).
    *   *Mitigation*: Use Beatty selection *within* priority bands, or use weighted tickets (Lottery) for coarse fairness and Beatty for fine-grained spacing. The current implementation uses Beatty to select *which* rank to run. This is primarily useful for avoiding starvation of low-priority tasks while still having a deterministic schedule.

### Sleeping Tasks

*   When a task sleeps, it is removed from the ready queue ($N$ decreases).
*   The counter $C$ continues incrementing.
*   When a task wakes, it is inserted back into the sorted ready queue.

### Real-Time and Latency

*   **Soft Real-Time**: The deterministic spacing helps predictability compared to random scheduling.
*   **Hard Real-Time**: Not guaranteed. A high-priority task might be at index 0, but if the current $B \mod N$ yields index $N-1$, the high-priority task waits.
*   **Preemption**: The scheduler should check if a newly woken high-priority task should preempt the current running task.

### NUMA / CPU Affinity

*   The `dag_task_t` structure should ideally contain affinity masks.
*   The `beatty_select` function should filter the ready queue to include only tasks eligible for the current CPU before sorting/selecting. This modifies $N$ per core.

## RCU Interactions

*   The ready queue can be protected by RCU for read-side access during selection.
*   Updates (insert/remove) happen under a lock, but the selection logic (reading the list) can be lock-free if the list structure supports it.

## Telemetry and Validation

To validate the scheduler's properties, the following metrics are exposed per task:

1.  **Schedule Count**: Number of times `beatty_select` picked this task.
2.  **Run Time**: Total CPU ticks consumed.
3.  **Latency**: Average time spent in `READY` state before transitioning to `RUNNING`.

These metrics allow verification of:
*   **Fairness**: Run time should be roughly equal (if 1/N share is the goal).
*   **Latency Distribution**: Should be smoother than Round Robin.
