# Commentary: The Nucleus and Scheduler

This chapter examines the core scheduling logic in `kernel/sched_beatty.c`, demonstrating the integration of mathematical fairness into the kernel nucleus.

## The Beatty Scheduler

The scheduler uses the properties of Beatty sequences to ensure fair allocation without complex runqueue balancing.

### Core Logic

The function `beatty_select` is the heart of the decision process.

```c
// kernel/sched_beatty.c

/**
 * Select next task to run using Beatty sequence
 * ...
 */
dag_task_t *beatty_select(
    beatty_scheduler_t *sched,
    dag_pdac_t *dag)
{
    if (sched == NULL || dag == NULL) {
        return NULL;
    }

    /* Step 1: Collect all READY tasks */
    // ... code omitted ...

    /* Step 3: Compute Beatty number B_α(counter) */
    uint64_t beatty_num = ((uint64_t)sched->counter * sched->alpha) >> 16;

    /* Step 4: Select task at position (beatty_num mod num_ready) */
    uint16_t selected_idx = beatty_num % num_ready;
    ready_task_t *selected = &ready_tasks[selected_idx];

    /* Step 5: Increment counter */
    sched->counter++;

    return selected->task;
}
```

### Commentary

1.  **State Independence**: The selection relies on `sched->counter` and `sched->alpha`. It doesn't need to track historical usage decay (unlike BSD schedulers), making it robust against history pollution.
2.  **O(1) Calculation**: The `beatty_num` calculation is a simple multiplication and shift (fixed-point arithmetic), ensuring constant time complexity regardless of load.
3.  **Fairness**: By using an irrational `alpha` (like the Golden Ratio), the sequence `floor(n * alpha)` distributes selection "hits" evenly over the integer domain, minimizing clustering (starvation).

## Invariants

This implementation satisfies **I10** (O(1) selection) and **I11** (Beatty fairness), as documented in `kernel/invariants.md`.
