/**
 * @file lcg.h
 * @brief Linear Congruential Generator (LCG) for Deterministic Randomness
 *
 * This file implements a classic Linear Congruential Generator for
 * pseudo-random number generation in the scheduler.
 *
 * ALGORITHM:
 * X[n+1] = (a * X[n] + c) mod m
 *
 * PARAMETERS (from Numerical Recipes in C):
 * - a = 1664525 (multiplier)
 * - c = 1013904223 (increment)
 * - m = 2^32 (modulus, implicit in uint32_t overflow)
 * - Period: 2^32 (~4 billion values)
 *
 * WHY LCG (not better RNGs)?
 * - **Fast**: 2 multiplications, 1 addition (no divisions!)
 * - **Deterministic**: Repeatable for testing/debugging
 * - **Sufficient**: Scheduler needs "good enough" randomness, not crypto
 * - **Proven**: Used in glibc rand(), POSIX drand48()
 *
 * REAL-WORLD USAGE:
 * - Monte Carlo simulations
 * - Game engines (procedural generation)
 * - Lottery scheduling (Waldspurger, 1994)
 * - Network jitter/backoff algorithms
 *
 * LIMITATIONS:
 * - **NOT cryptographically secure** (predictable)
 * - Lower bits have shorter periods (use upper bits)
 * - Correlations in low dimensions (not for crypto!)
 *
 * PEDAGOGICAL NOTE:
 * LCG demonstrates how simple arithmetic can generate apparently
 * random sequences. The full period depends on careful parameter
 * selection (Hull-Dobell theorem).
 *
 * @see kernel/lcg.c for implementation
 * @see Knuth, TAOCP Vol 2, Section 3.2 (random numbers)
 */

#ifndef LCG_H
#define LCG_H

#include <stdint.h>

/*******************************************************************************
 * CONSTANTS
 ******************************************************************************/

/**
 * LCG parameters (Numerical Recipes)
 */
#define LCG_A 1664525U       /* Multiplier */
#define LCG_C 1013904223U    /* Increment */
/* Modulus m = 2^32 is implicit in uint32_t wraparound */

/*******************************************************************************
 * TYPES
 ******************************************************************************/

/**
 * LCG state structure
 *
 * THREAD SAFETY:
 * - Each CPU/thread should have its own lcg_state_t
 * - No locking required (state is local)
 * - For global RNG, use per-CPU instances
 */
typedef struct lcg_state {
    uint32_t x;  /* Current state (seed) */
    uint64_t count;  /* Number of values generated (for debugging) */
} lcg_state_t;

/*******************************************************************************
 * CORE API
 ******************************************************************************/

/**
 * Initialize LCG with seed
 *
 * @param state LCG state to initialize
 * @param seed Initial seed value
 *
 * USAGE:
 * ```c
 * lcg_state_t rng;
 * lcg_init(&rng, 12345); // Deterministic sequence
 * ```
 *
 * SEED SELECTION:
 * - seed=0 is valid (generates full period)
 * - Use TSC/timestamp for non-deterministic sequences
 * - Use fixed seed for reproducible tests
 */
void lcg_init(lcg_state_t *state, uint32_t seed);

/**
 * Generate next pseudo-random value
 *
 * @param state LCG state
 * @return Pseudo-random uint32_t in [0, 2^32-1]
 *
 * ALGORITHM:
 * ```c
 * state->x = (LCG_A * state->x + LCG_C); // mod 2^32 implicit
 * return state->x;
 * ```
 *
 * TIME COMPLEXITY: O(1) (2 muls, 1 add)
 * SPACE COMPLEXITY: O(1)
 *
 * QUALITY:
 * - Passes chi-squared test
 * - Passes runs test
 * - Fails spectral test in high dimensions (not relevant for scheduler)
 */
uint32_t lcg_next(lcg_state_t *state);

/**
 * Generate random value in range [0, max)
 *
 * @param state LCG state
 * @param max Upper bound (exclusive)
 * @return Value in [0, max-1]
 *
 * ALGORITHM:
 * Uses rejection sampling to avoid modulo bias.
 *
 * EXAMPLE:
 * ```c
 * // Fair dice roll
 * uint32_t roll = lcg_range(&rng, 6) + 1; // Returns 1-6
 * ```
 *
 * MODULO BIAS:
 * Naive approach `lcg_next() % max` is biased if 2^32 not divisible by max.
 * We use rejection sampling: reject values >= (2^32 - (2^32 % max))
 */
uint32_t lcg_range(lcg_state_t *state, uint32_t max);

/**
 * Generate uniform random value in [0.0, 1.0)
 *
 * @param state LCG state
 * @return Double-precision float in [0.0, 1.0)
 *
 * ALGORITHM:
 * ```c
 * return lcg_next(state) / (double)(1ULL << 32);
 * ```
 *
 * PRECISION: ~2^-32 ≈ 2.3 × 10^-10
 *
 * USAGE:
 * ```c
 * if (lcg_uniform(&rng) < 0.8) {
 *     // 80% probability path
 * }
 * ```
 */
double lcg_uniform(lcg_state_t *state);

/*******************************************************************************
 * STATISTICAL TESTING
 ******************************************************************************/

/**
 * Chi-squared test for uniform distribution
 *
 * @param state LCG state
 * @param buckets Number of buckets (e.g., 10)
 * @param samples Number of samples to test (e.g., 10000)
 * @return Chi-squared statistic (< critical value = uniform)
 *
 * NULL HYPOTHESIS: Values are uniformly distributed
 * CRITICAL VALUE (10 buckets, α=0.05): 16.92
 *
 * If result < 16.92, we FAIL TO REJECT null hypothesis (uniform!)
 *
 * USAGE:
 * ```c
 * double chi2 = lcg_test_uniform(&rng, 10, 10000);
 * if (chi2 < 16.92) {
 *     printf("PASS: Uniform distribution\n");
 * }
 * ```
 */
double lcg_test_uniform(lcg_state_t *state, uint32_t buckets, uint32_t samples);

/**
 * Runs test for independence
 *
 * @param state LCG state
 * @param samples Number of samples
 * @return Z-score (|Z| < 1.96 = independent at α=0.05)
 *
 * Tests for serial correlation (are consecutive values independent?)
 *
 * RUN: Sequence of consecutive increasing or decreasing values
 * Example: [1,3,5,2,4,1] has 3 runs: up, up, down
 *
 * Expected runs: (2n - 1) / 3
 * Variance: (16n - 29) / 90
 *
 * Z-score: (observed - expected) / sqrt(variance)
 */
double lcg_test_runs(lcg_state_t *state, uint32_t samples);

/*******************************************************************************
 * DEBUGGING / INTROSPECTION
 ******************************************************************************/

/**
 * Get current state value
 *
 * @param state LCG state
 * @return Current state (for debugging)
 */
uint32_t lcg_get_state(const lcg_state_t *state);

/**
 * Get generation count
 *
 * @param state LCG state
 * @return Number of values generated
 */
uint64_t lcg_get_count(const lcg_state_t *state);

/**
 * Reset to initial seed
 *
 * @param state LCG state
 * @param seed New seed
 */
void lcg_reset(lcg_state_t *state, uint32_t seed);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Simulate coin flips
 *
 * Demonstrates binary random events with LCG.
 */
void example_coin_flips(void);

/**
 * Example: Lottery ticket selection
 *
 * Demonstrates weighted random selection (scheduler use case).
 */
void example_lottery_tickets(void);

/**
 * Example: Statistical validation
 *
 * Runs chi-squared and runs tests to validate LCG quality.
 */
void example_statistical_tests(void);

/**
 * Run all LCG examples
 */
void lcg_run_all_examples(void);

#endif /* LCG_H */
