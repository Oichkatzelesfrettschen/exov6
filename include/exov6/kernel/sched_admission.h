#pragma once

/**
 * @file sched_admission.h
 * @brief Stochastic Admission Control for DAG Scheduler
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Demonstrates how probability theory prevents system overload without
 * hard cutoffs. This is a key technique in distributed systems (Google Borg,
 * AWS Lambda) to gracefully degrade under load.
 *
 * THE OVERLOAD PROBLEM:
 * =====================
 * When tasks arrive faster than the system can schedule them:
 * - Reject all? (harsh, wastes resources)
 * - Accept all? (system thrashes, all tasks slow)
 * - Hard limit? (arbitrary cutoff, unfair)
 *
 * STOCHASTIC SOLUTION:
 * ====================
 * Use **probabilistic admission** based on current load:
 *   P(admit) = f(load)
 *
 * Where f is a smooth function (no hard cutoffs):
 *   Light load (load < 1.0): P ≈ 1.0 (accept almost everything)
 *   Heavy load (load > 2.0): P ≈ 0.1 (reject most, keep trying)
 *
 * ADMISSION FUNCTION:
 * ===================
 * We use the classic load-based admission:
 *   P(admit) = 1 / (1 + load)
 *
 * Examples:
 *   load = 0.1 → P = 0.91 (91% admitted)
 *   load = 0.5 → P = 0.67 (67% admitted)
 *   load = 1.0 → P = 0.50 (50% admitted)
 *   load = 2.0 → P = 0.33 (33% admitted)
 *   load = 9.0 → P = 0.10 (10% admitted)
 *
 * Properties:
 * - Always > 0 (never completely block)
 * - Monotonic decreasing (higher load → lower probability)
 * - Smooth (no discontinuities)
 *
 * MULTIDIMENSIONAL LOAD:
 * =======================
 * System has 8D resources (CPU, memory, I/O, ...).
 * We compute load as:
 *   load = ||used_resources|| / ||system_quota||
 *
 * Where ||·|| is octonion norm (already implemented).
 *
 * INTEGRATION WITH TOKEN BUCKETS:
 * ================================
 * Two-stage admission control:
 *
 * Stage 1: Token bucket (hard quota)
 *   - If tokens available: ADMIT (deterministic)
 *   - Else: go to Stage 2
 *
 * Stage 2: Stochastic admission (soft limit)
 *   - Compute load
 *   - Admit with probability P(load)
 *   - Graceful degradation
 *
 * This combines **hard guarantees** (token bucket) with
 * **graceful overload** (stochastic admission).
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - **Google Borg**: Quota-based admission with priority preemption
 * - **AWS Lambda**: Concurrency limits with throttling
 * - **Kubernetes**: ResourceQuotas with QoS classes
 * - **TCP congestion control**: AIMD (additive increase, multiplicative decrease)
 *
 * EXAMPLE SCENARIO:
 * =================
 * System quota: CPU=4.0, MEM=1024
 * Running tasks: CPU=3.5, MEM=900  →  load ≈ 0.88
 *
 * New task arrives: CPU=1.0, MEM=200
 *
 * Stage 1: Check token bucket
 *   - Would exceed quota? YES (CPU=4.5 > 4.0)
 *   - Go to Stage 2
 *
 * Stage 2: Stochastic admission
 *   - load = 0.88 → P = 1/(1+0.88) ≈ 0.53
 *   - Random = 0.42 < 0.53? YES → ADMIT
 *   - (But only 53% of similar tasks get admitted)
 */

#include "types.h"
#include "dag_pdac.h"
#include "token_bucket.h"
#include "lcg.h"

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/**
 * Minimum admission probability (never completely block)
 */
#define ADMISSION_MIN_PROBABILITY Q16(0.01)  /* 1% */

/**
 * Maximum admission probability (cap at 100%)
 */
#define ADMISSION_MAX_PROBABILITY Q16(1.0)   /* 100% */

/*******************************************************************************
 * ADMISSION CONTROL STATE
 ******************************************************************************/

/**
 * Admission control state
 *
 * Manages quota (token bucket) and stochastic admission (load-based).
 */
typedef struct admission_control {
    /* Hard quota (token bucket) */
    token_bucket_t quota;                     /* System-wide token bucket */
    resource_vector_t system_capacity;        /* Total system resources */

    /* Random number generator (for stochastic decisions) */
    lcg_state_t *rng;                         /* LCG for admission probability */

    /* Statistics */
    uint64_t total_attempts;                  /* Total admission attempts */
    uint64_t token_admits;                    /* Admitted via token bucket */
    uint64_t stochastic_admits;               /* Admitted via stochastic */
    uint64_t rejections;                      /* Rejected tasks */

    /* Load tracking */
    q16_t current_load;                       /* Cached load value */
} admission_control_t;

/*******************************************************************************
 * CORE API
 ******************************************************************************/

/**
 * Initialize admission control
 *
 * @param ac            Admission control state
 * @param rng           Random number generator
 * @param capacity      System resource capacity (8D vector)
 * @param refill_rate   Token bucket refill rate (resources per tick)
 * @param burst_size    Token bucket burst size (max accumulated)
 */
void admission_init(
    admission_control_t *ac,
    lcg_state_t *rng,
    resource_vector_t capacity,
    resource_vector_t refill_rate,
    resource_vector_t burst_size
);

/**
 * Try to admit a task
 *
 * Two-stage admission:
 * 1. Check token bucket (hard quota)
 * 2. If insufficient tokens, stochastic admission (soft limit)
 *
 * @param ac    Admission control state
 * @param dag   DAG (for computing current load)
 * @param task  Task to admit
 * @return      1 if admitted, 0 if rejected
 */
int admission_try_admit(
    admission_control_t *ac,
    const dag_pdac_t *dag,
    const dag_task_t *task
);

/**
 * Release resources when task completes
 *
 * Returns tokens to bucket (if applicable).
 *
 * @param ac    Admission control state
 * @param task  Completed task
 */
void admission_release(
    admission_control_t *ac,
    const dag_task_t *task
);

/**
 * Refill token bucket (called periodically)
 *
 * @param ac      Admission control state
 * @param dt_ms   Time delta in milliseconds
 */
void admission_refill(
    admission_control_t *ac,
    uint32_t dt_ms
);

/*******************************************************************************
 * LOAD COMPUTATION
 ******************************************************************************/

/**
 * Compute current system load
 *
 * Load = ||running_resources|| / ||capacity||
 *
 * Where ||·|| is octonion norm.
 *
 * @param ac   Admission control state
 * @param dag  DAG (contains running tasks)
 * @return     Load value (Q16 fixed-point)
 */
q16_t admission_compute_load(
    const admission_control_t *ac,
    const dag_pdac_t *dag
);

/**
 * Compute admission probability from load
 *
 * Formula: P = 1 / (1 + load)
 *
 * @param load  Current load (Q16 fixed-point)
 * @return      Admission probability (Q16 fixed-point, [0.0, 1.0])
 */
q16_t admission_compute_probability(q16_t load);

/*******************************************************************************
 * STATISTICS & INTROSPECTION
 ******************************************************************************/

/**
 * Get total admission attempts
 */
uint64_t admission_get_total_attempts(const admission_control_t *ac);

/**
 * Get number of tasks admitted via token bucket
 */
uint64_t admission_get_token_admits(const admission_control_t *ac);

/**
 * Get number of tasks admitted via stochastic admission
 */
uint64_t admission_get_stochastic_admits(const admission_control_t *ac);

/**
 * Get number of rejected tasks
 */
uint64_t admission_get_rejections(const admission_control_t *ac);

/**
 * Get admission rate (admitted / total)
 *
 * @return  Admission rate (Q16 fixed-point, [0.0, 1.0])
 */
q16_t admission_get_rate(const admission_control_t *ac);

/**
 * Get current system load (cached)
 */
q16_t admission_get_current_load(const admission_control_t *ac);

/**
 * Print admission control statistics
 */
void admission_print_stats(const admission_control_t *ac);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Demonstrate admission probability curve
 *
 * Shows how P(admit) changes with load.
 */
void example_admission_probability_curve(void);

/**
 * Example: Two-stage admission (token + stochastic)
 *
 * Demonstrates hard quota + soft limit behavior.
 */
void example_admission_two_stage(void);

/**
 * Example: Graceful degradation under overload
 *
 * Shows that system continues accepting some tasks even at high load.
 */
void example_admission_overload(void);

/**
 * Example: 8D load computation
 *
 * Demonstrates multidimensional resource load calculation.
 */
void example_admission_multidimensional_load(void);

/**
 * Run all admission control examples
 */
void admission_run_all_examples(void);
