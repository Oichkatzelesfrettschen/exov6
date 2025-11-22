# Beatty Sequence Scheduler

This document describes the **Beatty Sequence Scheduler**, a deterministic, quasi-random scheduler implemented in the Phoenix Exokernel (`kernel/sched_beatty.c`).

## 1. Theoretical Foundation

The scheduler is based on the **Beatty Sequence**, defined for an irrational number $\alpha > 1$ (typically the Golden Ratio $\phi \approx 1.618$) as:

$$ B_\alpha(n) = \lfloor n \alpha \rfloor $$

This sequence generates a spectrum of values that are evenly distributed but non-periodic (quasi-random).

## 2. Algorithm

The scheduler maps the Beatty sequence to task selection to achieve fair, deterministic scheduling with low jitter.

### Task Selection
1.  **Identify Ready Tasks**: Collect all tasks in `TASK_STATE_READY`.
2.  **Prioritize**: Sort tasks by priority. Priority is calculated as the L2 norm (Euclidean length) of the task's resource vector (`resource_vector_norm`).
    *   $P = \sqrt{cpu^2 + mem^2 + ...}$
3.  **Compute Index**: Calculate the next Beatty number for the current counter step $n$.
    *   $k = \lfloor n \cdot \alpha \rfloor \pmod{\text{num\_ready}}$
4.  **Select**: Run the task at index $k$ in the sorted list.
5.  **Advance**: Increment $n$.

## 3. Properties

### 3.1. Determinism
Given the same set of ready tasks and the same initial counter state, the scheduler produces an identical schedule. This is crucial for debugging and real-time analysis.

### 3.2. The Three-Distance Theorem
The gaps between successive selections of a specific task in the Beatty sequence take on at most three distinct values. This provides a strong bound on **jitter**: a task will not be starved for arbitrary periods; its inter-arrival times are bounded.

### 3.3. Fairness vs. Priority
*   **Fairness**: The modulo operation ensures every slot in the ready list is visited eventually.
*   **Priority**: Sorting by priority ensures that higher-priority tasks (at the start of the list) are mapped to specific "windows" of the Beatty sequence. While not a strict priority scheduler (which would starve low priority), it biases selection towards high-priority tasks while guaranteeing liveness for all.

## 4. Implementation Details

*   **Fixed Point Arithmetic**: $\alpha$ is stored as a Q16.16 fixed-point number (`alpha`).
*   **State**:
    *   `counter`: Monotonically increasing step counter.
    *   `selections`: Statistics tracking.
*   **Introspection**: The scheduler supports gap analysis (`beatty_analyze_gaps`) to verify the three-distance property at runtime.
