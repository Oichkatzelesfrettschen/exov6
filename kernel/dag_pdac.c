/**
 * @file dag_pdac.c
 * @brief PDAC DAG Implementation: Path Composition and Deadlock Detection
 */

#include "types.h"
#include "defs.h"
#include "dag_pdac.h"
#include "resource_vector.h"
#include "q16_fixed.h"

/* ============================================================================
 * DAG CONSTRUCTION
 * ============================================================================ */

/**
 * Initialize empty DAG
 */
void pdac_dag_init(dag_pdac_t *dag, resource_vector_t system_quota) {
    dag->num_tasks = 0;
    dag->system_quota = system_quota;
    dag->available = system_quota;

    /* Clear all task slots */
    for (int i = 0; i < DAG_MAX_TASKS; i++) {
        dag->tasks[i].id = 0;
        dag->tasks[i].state = TASK_STATE_PENDING;
        dag->tasks[i].num_deps = 0;
    }
}

/**
 * Add task to DAG
 *
 * Returns: Task ID on success, -1 on failure
 */
int pdac_dag_add_task(
    dag_pdac_t *dag,
    const char *name,
    resource_vector_t resources
) {
    if (dag->num_tasks >= DAG_MAX_TASKS) {
        return -1;  /* DAG full */
    }

    uint16_t task_id = dag->num_tasks;
    dag_task_t *task = &dag->tasks[task_id];

    /* Initialize task */
    task->id = task_id;
    safestrcpy(task->name, name, sizeof(task->name));
    task->resources = resources;
    task->num_deps = 0;
    task->state = TASK_STATE_PENDING;
    task->priority = resource_vector_norm(resources);
    task->start_time = 0;
    task->end_time = 0;

    dag->num_tasks++;
    return task_id;
}

/**
 * Cycle detection helper (DFS)
 */
static int pdac_dag_has_cycle_dfs(
    dag_pdac_t *dag,
    uint16_t node,
    uint8_t *visited,
    uint8_t *rec_stack
) {
    if (rec_stack[node]) {
        return 1;  /* Cycle detected */
    }

    if (visited[node]) {
        return 0;  /* Already processed */
    }

    visited[node] = 1;
    rec_stack[node] = 1;

    /* Check all dependencies */
    dag_task_t *task = &dag->tasks[node];
    for (uint8_t i = 0; i < task->num_deps; i++) {
        uint16_t dep = task->deps[i];
        if (pdac_dag_has_cycle_dfs(dag, dep, visited, rec_stack)) {
            return 1;
        }
    }

    rec_stack[node] = 0;
    return 0;
}

/**
 * Add dependency: task_id depends on dep_id
 *
 * Ensures DAG property (no cycles)
 */
int pdac_dag_add_dependency(
    dag_pdac_t *dag,
    uint16_t task_id,
    uint16_t dep_id
) {
    /* Validate task IDs */
    if (task_id >= dag->num_tasks || dep_id >= dag->num_tasks) {
        return -1;
    }

    dag_task_t *task = &dag->tasks[task_id];

    /* Check max dependencies */
    if (task->num_deps >= DAG_MAX_DEPS) {
        return -1;
    }

    /* Add dependency */
    task->deps[task->num_deps++] = dep_id;

    /* Check for cycles using DFS */
    uint8_t visited[DAG_MAX_TASKS] = {0};
    uint8_t rec_stack[DAG_MAX_TASKS] = {0};

    if (pdac_dag_has_cycle_dfs(dag, task_id, visited, rec_stack)) {
        /* Cycle detected - remove dependency and fail */
        task->num_deps--;
        return -1;
    }

    return 0;
}

/* ============================================================================
 * DAG PATH COMPOSITION
 * ============================================================================ */

/**
 * Compose path through DAG using octonion multiplication
 *
 * **NON-ASSOCIATIVE**: Different evaluation orders yield different results!
 */
resource_vector_t pdac_dag_compose_path(
    dag_pdac_t *dag,
    uint16_t *path,
    uint16_t path_len
) {
    if (path_len == 0) {
        return RESOURCE_VEC_ZERO;
    }

    /* Start with first task's resources */
    resource_vector_t result = dag->tasks[path[0]].resources;

    /* Compose left-to-right: ((A * B) * C) * D ... */
    for (uint16_t i = 1; i < path_len; i++) {
        resource_vector_t next = dag->tasks[path[i]].resources;
        result = resource_vector_compose(result, next);
    }

    return result;
}

/**
 * Demonstrate non-associativity of path composition
 *
 * Computes:
 * - Left-associative:  (A * B) * C
 * - Right-associative: A * (B * C)
 *
 * Returns: 1 if results differ, 0 if same
 */
int pdac_pdac_dag_demonstrate_nonassociativity(
    dag_pdac_t *dag,
    uint16_t task_a,
    uint16_t task_b,
    uint16_t task_c,
    resource_vector_t *out_left,
    resource_vector_t *out_right
) {
    /* Validate task IDs */
    if (task_a >= dag->num_tasks ||
        task_b >= dag->num_tasks ||
        task_c >= dag->num_tasks) {
        return -1;
    }

    resource_vector_t a = dag->tasks[task_a].resources;
    resource_vector_t b = dag->tasks[task_b].resources;
    resource_vector_t c = dag->tasks[task_c].resources;

    /* Left-associative: (A * B) * C */
    resource_vector_t ab = resource_vector_compose(a, b);
    *out_left = resource_vector_compose(ab, c);

    /* Right-associative: A * (B * C) */
    resource_vector_t bc = resource_vector_compose(b, c);
    *out_right = resource_vector_compose(a, bc);

    /* Compare norms (close enough for Q16.16 precision) */
    q16_t norm_left = resource_vector_norm(*out_left);
    q16_t norm_right = resource_vector_norm(*out_right);

    /* Threshold: difference > 0.01 in Q16.16 */
    q16_t diff = (norm_left > norm_right) ?
                 (norm_left - norm_right) :
                 (norm_right - norm_left);

    #define NONASSOC_THRESHOLD (Q16_ONE / 100)

    return (diff > NONASSOC_THRESHOLD) ? 1 : 0;
}

/* ============================================================================
 * DEADLOCK DETECTION
 * ============================================================================ */

/**
 * Check if specific task pair is orthogonal (potential deadlock)
 */
int pdac_dag_check_task_orthogonality(
    dag_pdac_t *dag,
    uint16_t task1,
    uint16_t task2
) {
    if (task1 >= dag->num_tasks || task2 >= dag->num_tasks) {
        return 0;
    }

    return resource_vector_is_orthogonal(
        dag->tasks[task1].resources,
        dag->tasks[task2].resources
    );
}

/**
 * Detect resource deadlocks using zero divisor property
 *
 * Checks all pairs of PENDING/READY tasks for orthogonal resources
 */
deadlock_info_t pdac_dag_detect_deadlock(dag_pdac_t *dag) {
    deadlock_info_t info = {0};

    /* Check all pairs of non-completed tasks */
    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        if (dag->tasks[i].state == TASK_STATE_COMPLETED ||
            dag->tasks[i].state == TASK_STATE_FAILED) {
            continue;
        }

        for (uint16_t j = i + 1; j < dag->num_tasks; j++) {
            if (dag->tasks[j].state == TASK_STATE_COMPLETED ||
                dag->tasks[j].state == TASK_STATE_FAILED) {
                continue;
            }

            /* Check if tasks are orthogonal (zero divisor) */
            if (pdac_dag_check_task_orthogonality(dag, i, j)) {
                info.detected = 1;
                info.task1 = i;
                info.task2 = j;

                snprintf(info.reason, sizeof(info.reason),
                         "Tasks '%s' and '%s' have orthogonal resource requirements. "
                         "Composition ≈ 0 (zero divisor) → potential deadlock.",
                         dag->tasks[i].name,
                         dag->tasks[j].name);

                return info;
            }
        }
    }

    /* No deadlock detected */
    info.detected = 0;
    snprintf(info.reason, sizeof(info.reason), "No deadlock detected");
    return info;
}

/* ============================================================================
 * DAG SCHEDULING
 * ============================================================================ */

/**
 * Check if all dependencies of a task are satisfied
 */
static int pdac_dag_deps_satisfied(dag_pdac_t *dag, uint16_t task_id) {
    dag_task_t *task = &dag->tasks[task_id];

    for (uint8_t i = 0; i < task->num_deps; i++) {
        uint16_t dep_id = task->deps[i];
        if (dag->tasks[dep_id].state != TASK_STATE_COMPLETED) {
            return 0;  /* Dependency not satisfied */
        }
    }

    return 1;  /* All dependencies satisfied */
}

/**
 * Find next ready task to execute
 *
 * Selects highest-priority task where:
 * 1. All dependencies satisfied
 * 2. Resources available
 *
 * Returns: Task ID, or -1 if no task ready
 */
int pdac_dag_get_next_ready_task(dag_pdac_t *dag) {
    int best_task = -1;
    q16_t best_priority = 0;

    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        dag_task_t *task = &dag->tasks[i];

        /* Skip non-pending tasks */
        if (task->state != TASK_STATE_PENDING) {
            continue;
        }

        /* Check dependencies */
        if (!pdac_dag_deps_satisfied(dag, i)) {
            continue;
        }

        /* Check resource availability */
        if (!resource_vector_fits(task->resources, dag->available)) {
            continue;
        }

        /* Select highest priority */
        if (best_task == -1 || task->priority > best_priority) {
            best_task = i;
            best_priority = task->priority;
        }
    }

    return best_task;
}

/**
 * Mark task as running and allocate resources
 */
int pdac_dag_start_task(dag_pdac_t *dag, uint16_t task_id) {
    if (task_id >= dag->num_tasks) {
        return -1;
    }

    dag_task_t *task = &dag->tasks[task_id];

    /* Allocate resources */
    if (!resource_vector_allocate(&dag->available, task->resources)) {
        return -1;  /* Insufficient resources */
    }

    task->state = TASK_STATE_RUNNING;
    /* In real kernel, would set task->start_time = timer_ticks() */

    return 0;
}

/**
 * Mark task as completed and release resources
 */
void pdac_dag_complete_task(dag_pdac_t *dag, uint16_t task_id) {
    if (task_id >= dag->num_tasks) {
        return;
    }

    dag_task_t *task = &dag->tasks[task_id];

    /* Release resources */
    resource_vector_release(&dag->available, task->resources);

    task->state = TASK_STATE_COMPLETED;
    /* In real kernel, would set task->end_time = timer_ticks() */
}

/**
 * Check if DAG is fully completed
 */
int pdac_dag_is_complete(dag_pdac_t *dag) {
    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        if (dag->tasks[i].state != TASK_STATE_COMPLETED) {
            return 0;
        }
    }
    return 1;
}

/* ============================================================================
 * DEBUGGING AND VISUALIZATION
 * ============================================================================ */

/**
 * Print task details
 */
void pdac_dag_print_task(dag_pdac_t *dag, uint16_t task_id) {
    if (task_id >= dag->num_tasks) {
        return;
    }

    dag_task_t *task = &dag->tasks[task_id];

    const char *state_str[] = {
        "PENDING", "READY", "RUNNING", "COMPLETED", "FAILED"
    };

    cprintf("  Task %d: %s [%s]\n",
            task->id,
            task->name,
            state_str[task->state]);

    resource_vector_print(task->resources, "    Resources");

    if (task->num_deps > 0) {
        cprintf("    Dependencies: ");
        for (uint8_t i = 0; i < task->num_deps; i++) {
            cprintf("%d ", task->deps[i]);
        }
        cprintf("\n");
    }

    char priority_str[32];
    int int_part = q16_to_int(task->priority);
    int frac_part = ((task->priority & 0xFFFF) * 100) >> 16;
    snprintf(priority_str, sizeof(priority_str), "%d.%02d", int_part, frac_part);
    cprintf("    Priority: %s\n", priority_str);
}

/**
 * Print DAG task graph
 */
void pdac_dag_print(dag_pdac_t *dag, const char *label) {
    if (label) {
        cprintf("\n=== %s ===\n", label);
    }

    cprintf("DAG: %d tasks\n", dag->num_tasks);
    resource_vector_print(dag->system_quota, "System Quota");
    resource_vector_print(dag->available, "Available Resources");

    cprintf("\nTasks:\n");
    for (uint16_t i = 0; i < dag->num_tasks; i++) {
        pdac_dag_print_task(dag, i);
    }
}

/**
 * Print path composition result
 */
void pdac_dag_print_path_composition(
    dag_pdac_t *dag,
    uint16_t *path,
    uint16_t path_len,
    resource_vector_t result
) {
    cprintf("Path: ");
    for (uint16_t i = 0; i < path_len; i++) {
        if (i > 0) cprintf(" → ");
        cprintf("%s", dag->tasks[path[i]].name);
    }
    cprintf("\n");

    resource_vector_print(result, "Composed Result");
}

/* ============================================================================
 * PEDAGOGICAL EXAMPLES (compiled in debug mode)
 * ============================================================================ */

#ifdef DEBUG

/**
 * Example 1: Path-dependent scheduling (Non-associativity)
 */
void pdac_example_dag_path_dependence(void) {
    cprintf("\n=== Example 1: Path-Dependent Scheduling (Non-Associativity) ===\n");

    /* Create DAG with system quota */
    dag_pdac_t dag;
    resource_vector_t quota = RESOURCE_VEC(10000, 16384, 1000, 10000, 0, 1000, 1000, 100);
    pdac_dag_init(dag_init(&dag, quota)dag, quota);

    /* Add three tasks with different resource profiles */
    int task_a = pdac_dag_add_task(dag_add_task(&dag,dag, "WebServer",
                              RESOURCE_VEC(100, 512, 50, 1000, 0, 100, 50, 10));
    int task_b = pdac_dag_add_task(dag_add_task(&dag,dag, "Database",
                              RESOURCE_VEC(200, 4096, 200, 500, 0, 500, 100, 5));
    int task_c = pdac_dag_add_task(dag_add_task(&dag,dag, "Analytics",
                              RESOURCE_VEC(500, 2048, 100, 200, 0, 200, 50, 3));

    pdac_dag_print_task(dag_print_task(&dag,dag, task_a);
    pdac_dag_print_task(dag_print_task(&dag,dag, task_b);
    pdac_dag_print_task(dag_print_task(&dag,dag, task_c);

    /* Demonstrate non-associativity */
    resource_vector_t left_assoc, right_assoc;
    int is_nonassoc = pdac_dag_demonstrate_nonassociativity(
        &dag, task_a, task_b, task_c,
        &left_assoc, &right_assoc
    );

    cprintf("\nPath Composition:\n");
    resource_vector_print(left_assoc, "  (WebServer * Database) * Analytics");
    resource_vector_print(right_assoc, "  WebServer * (Database * Analytics)");

    q16_t norm_left = resource_vector_norm(left_assoc);
    q16_t norm_right = resource_vector_norm(right_assoc);

    char norm_left_str[32], norm_right_str[32];
    int int_l = q16_to_int(norm_left);
    int frac_l = ((norm_left & 0xFFFF) * 100) >> 16;
    int int_r = q16_to_int(norm_right);
    int frac_r = ((norm_right & 0xFFFF) * 100) >> 16;

    snprintf(norm_left_str, sizeof(norm_left_str), "%d.%02d", int_l, frac_l);
    snprintf(norm_right_str, sizeof(norm_right_str), "%d.%02d", int_r, frac_r);

    cprintf("  Left-associative norm:  %s\n", norm_left_str);
    cprintf("  Right-associative norm: %s\n", norm_right_str);

    if (is_nonassoc) {
        cprintf("\n✓ NON-ASSOCIATIVE: Execution order affects resource usage!\n");
        cprintf("  This is a FEATURE of PDAC:\n");
        cprintf("  - DAG scheduling is path-dependent\n");
        cprintf("  - Octonion algebra models this naturally\n");
        cprintf("  - Scheduler can choose optimal evaluation order\n");
    } else {
        cprintf("\n  Paths are equivalent (rare edge case)\n");
    }

    cprintf("\n");
}

/**
 * Example 2: Deadlock detection via zero divisors
 */
void pdac_example_dag_deadlock_detection(void) {
    cprintf("\n=== Example 2: Deadlock Detection via Zero Divisors ===\n");

    /* Create DAG */
    dag_pdac_t dag;
    resource_vector_t quota = RESOURCE_VEC(10000, 16384, 1000, 10000, 0, 1000, 1000, 100);
    pdac_dag_init(dag_init(&dag, quota)dag, quota);

    /* Task A: CPU-intensive (high CPU, zero memory) */
    int task_a = pdac_dag_add_task(dag_add_task(&dag,dag, "CPUBound",
                              RESOURCE_VEC(5000, 10, 0, 0, 0, 0, 0, 0));

    /* Task B: Memory-intensive (zero CPU, high memory) */
    int task_b = pdac_dag_add_task(dag_add_task(&dag,dag, "MemBound",
                              RESOURCE_VEC(10, 8192, 0, 0, 0, 0, 0, 0));

    /* Task C: Balanced workload */
    int task_c = pdac_dag_add_task(dag_add_task(&dag,dag, "Balanced",
                              RESOURCE_VEC_BALANCED);

    cprintf("\nTasks:\n");
    pdac_dag_print_task(dag_print_task(&dag,dag, task_a);
    pdac_dag_print_task(dag_print_task(&dag,dag, task_b);
    pdac_dag_print_task(dag_print_task(&dag,dag, task_c);

    /* Check for deadlocks */
    cprintf("\nDeadlock Analysis:\n");

    if (pdac_dag_check_task_orthogonality(dag_check_task_orthogonality(&dag,dag, task_a, task_b)) {
        cprintf("  ⚠️  WARNING: CPUBound and MemBound are ORTHOGONAL\n");
        cprintf("     Composition ≈ 0 (zero divisor)\n");
        cprintf("     Potential DEADLOCK if both acquire exclusive resources!\n");
        cprintf("     Explanation: Non-overlapping resource requirements\n");
    } else {
        cprintf("  ✓ CPUBound and MemBound can coexist\n");
    }

    if (pdac_dag_check_task_orthogonality(dag_check_task_orthogonality(&dag,dag, task_a, task_c)) {
        cprintf("  ⚠️  WARNING: CPUBound and Balanced are ORTHOGONAL\n");
    } else {
        cprintf("  ✓ CPUBound and Balanced can coexist\n");
    }

    if (pdac_dag_check_task_orthogonality(dag_check_task_orthogonality(&dag,dag, task_b, task_c)) {
        cprintf("  ⚠️  WARNING: MemBound and Balanced are ORTHOGONAL\n");
    } else {
        cprintf("  ✓ MemBound and Balanced can coexist\n");
    }

    /* Run full deadlock detection */
    deadlock_info_t deadlock = pdac_dag_detect_deadlock(dag_detect_deadlock(&dag)dag);
    if (deadlock.detected) {
        cprintf("\n❌ DEADLOCK DETECTED:\n");
        cprintf("   %s\n", deadlock.reason);
    } else {
        cprintf("\n✓ No deadlock detected\n");
    }

    cprintf("\n");
}

/**
 * Example 3: DAG scheduler simulation
 */
void pdac_example_dag_scheduler(void) {
    cprintf("\n=== Example 3: DAG Scheduler Simulation ===\n");

    /* Create DAG with realistic system quota */
    dag_pdac_t dag;
    resource_vector_t quota = RESOURCE_VEC(10000, 16384, 1000, 10000, 0, 1000, 1000, 100);
    pdac_dag_init(dag_init(&dag, quota)dag, quota);

    /* Build task dependency graph:
     *
     *   Task A (Web Frontend)
     *     ├─> Task B (API Server)
     *     │     └─> Task D (Cache)
     *     └─> Task C (Auth Service)
     *           └─> Task D (Cache)
     *
     * Execution order: D → B,C (parallel) → A
     */

    int task_a = pdac_dag_add_task(dag_add_task(&dag,dag, "WebFrontend",
                              RESOURCE_VEC(200, 1024, 100, 2000, 0, 100, 100, 5));
    int task_b = pdac_dag_add_task(dag_add_task(&dag,dag, "APIServer",
                              RESOURCE_VEC(500, 2048, 200, 1000, 0, 200, 50, 10));
    int task_c = pdac_dag_add_task(dag_add_task(&dag,dag, "AuthService",
                              RESOURCE_VEC(300, 1024, 50, 500, 0, 50, 50, 8));
    int task_d = pdac_dag_add_task(dag_add_task(&dag,dag, "CacheLayer",
                              RESOURCE_VEC(100, 4096, 500, 200, 0, 500, 20, 3));

    /* Add dependencies */
    pdac_dag_add_dependency(dag_add_dependency(&dag,dag, task_a, task_b);  /* A depends on B */
    pdac_dag_add_dependency(dag_add_dependency(&dag,dag, task_a, task_c);  /* A depends on C */
    pdac_dag_add_dependency(dag_add_dependency(&dag,dag, task_b, task_d);  /* B depends on D */
    pdac_dag_add_dependency(dag_add_dependency(&dag,dag, task_c, task_d);  /* C depends on D */

    cprintf("\nInitial DAG:\n");
    pdac_dag_print(dag_print(&dag,dag, NULL);

    /* Check for deadlocks before execution */
    deadlock_info_t deadlock = pdac_dag_detect_deadlock(dag_detect_deadlock(&dag)dag);
    if (deadlock.detected) {
        cprintf("\n❌ DEADLOCK DETECTED - aborting execution\n");
        cprintf("   %s\n", deadlock.reason);
        return;
    }

    /* Simulate DAG execution */
    cprintf("\n=== Simulating DAG Execution ===\n");
    int step = 0;

    while (!pdac_dag_is_complete(dag_is_complete(&dag)dag)) {
        cprintf("\n--- Step %d ---\n", ++step);

        /* Get next ready task */
        int next_task = pdac_dag_get_next_ready_task(dag_get_next_ready_task(&dag)dag);

        if (next_task == -1) {
            cprintf("No task ready (waiting for resources or dependencies)\n");
            break;
        }

        /* Start task */
        cprintf("Starting task: %s\n", dag.tasks[next_task].name);
        if (pdac_dag_start_task(dag_start_task(&dag,dag, next_task) < 0) {
            cprintf("ERROR: Failed to start task (insufficient resources)\n");
            break;
        }

        resource_vector_print(dag.available, "Available Resources");

        /* Simulate task completion immediately (for demo) */
        pdac_dag_complete_task(dag_complete_task(&dag,dag, next_task);
        cprintf("Completed task: %s\n", dag.tasks[next_task].name);

        resource_vector_print(dag.available, "Available Resources");
    }

    if (pdac_dag_is_complete(dag_is_complete(&dag)dag)) {
        cprintf("\n✓ DAG EXECUTION COMPLETE\n");
        cprintf("  All %d tasks finished successfully\n", dag.num_tasks);
    } else {
        cprintf("\n❌ DAG EXECUTION INCOMPLETE\n");
    }

    cprintf("\n");
}

/**
 * Run all DAG pedagogical examples
 */
void pdac_dag_run_examples(void) {
    cprintf("\n");
    cprintf("╔═══════════════════════════════════════════════════════════╗\n");
    cprintf("║  PDAC DAG: Path Composition & Deadlock Detection         ║\n");
    cprintf("║  Pedagogical Examples                                    ║\n");
    cprintf("╚═══════════════════════════════════════════════════════════╝\n");

    pdac_example_dag_path_dependence();
    pdac_example_dag_deadlock_detection();
    pdac_example_dag_scheduler();

    cprintf("╔═══════════════════════════════════════════════════════════╗\n");
    cprintf("║  DAG Examples Complete                                   ║\n");
    cprintf("║  See PDAC_UNIFIED_FRAMEWORK.md for detailed explanation ║\n");
    cprintf("╚═══════════════════════════════════════════════════════════╝\n");
    cprintf("\n");
}

#endif /* DEBUG */
