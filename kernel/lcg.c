/**
 * @file lcg.c
 * @brief Linear Congruential Generator Implementation
 *
 * @see include/lcg.h for API documentation
 */

#include "lcg.h"
#include "printf.h"
#include <stdint.h>
#include <math.h>

/*******************************************************************************
 * CORE API IMPLEMENTATION
 ******************************************************************************/

/**
 * Initialize LCG with seed
 */
void lcg_init(lcg_state_t *state, uint32_t seed)
{
    if (state == NULL) {
        return;
    }

    state->x = seed;
    state->count = 0;
}

/**
 * Generate next pseudo-random value
 *
 * PERFORMANCE:
 * - 2 multiplications (32-bit × 32-bit)
 * - 1 addition
 * - ~5-10 CPU cycles on modern processors
 */
uint32_t lcg_next(lcg_state_t *state)
{
    if (state == NULL) {
        return 0;
    }

    /* LCG formula: X[n+1] = (a * X[n] + c) mod 2^32 */
    state->x = (LCG_A * state->x + LCG_C);
    state->count++;

    return state->x;
}

/**
 * Generate random value in range [0, max)
 *
 * REJECTION SAMPLING:
 * To avoid modulo bias, we reject values that would cause unfair distribution.
 *
 * Example: max=3, 2^32=10 (simplified)
 * Without rejection: 0,1,2,3,4,5,6,7,8,9 → 0,1,2,0,1,2,0,1,2,0
 * 0 appears 4 times, 1 and 2 appear 3 times (BIASED!)
 *
 * With rejection: Reject 9 (>= threshold), keep 0-8
 * 0,1,2,0,1,2,0,1,2 → Fair distribution
 */
uint32_t lcg_range(lcg_state_t *state, uint32_t max)
{
    if (state == NULL || max == 0) {
        return 0;
    }

    if (max == 1) {
        return 0; /* Trivial case */
    }

    /* Calculate threshold for rejection sampling */
    uint64_t range_max = (1ULL << 32); /* 2^32 */
    uint64_t threshold = range_max - (range_max % max);

    /* Rejection sampling loop */
    uint32_t val;
    do {
        val = lcg_next(state);
    } while (val >= threshold);

    return val % max;
}

/**
 * Generate uniform random value in [0.0, 1.0)
 *
 * PRECISION:
 * - Divisor: 2^32 = 4,294,967,296
 * - Smallest step: ~2.3 × 10^-10
 * - More than sufficient for scheduler decisions
 */
double lcg_uniform(lcg_state_t *state)
{
    if (state == NULL) {
        return 0.0;
    }

    uint32_t val = lcg_next(state);

    /* Divide by 2^32 to get [0.0, 1.0) */
    return (double)val / (double)(1ULL << 32);
}

/*******************************************************************************
 * STATISTICAL TESTING
 ******************************************************************************/

/**
 * Chi-squared test for uniform distribution
 *
 * ALGORITHM:
 * 1. Generate N samples
 * 2. Count how many fall in each bucket
 * 3. Compare observed vs. expected (N/buckets)
 * 4. Compute χ² = Σ((observed - expected)² / expected)
 *
 * INTERPRETATION:
 * - χ² < critical value → uniform distribution
 * - χ² > critical value → non-uniform (biased)
 */
double lcg_test_uniform(lcg_state_t *state, uint32_t buckets, uint32_t samples)
{
    if (state == NULL || buckets == 0 || samples == 0) {
        return -1.0;
    }

    /* Allocate bucket counters (stack array, limited size) */
    uint32_t counts[256] = {0};
    if (buckets > 256) {
        printf("Warning: Too many buckets (max 256)\n");
        buckets = 256;
    }

    /* Generate samples and count */
    for (uint32_t i = 0; i < samples; i++) {
        uint32_t val = lcg_range(state, buckets);
        counts[val]++;
    }

    /* Compute chi-squared statistic */
    double expected = (double)samples / (double)buckets;
    double chi2 = 0.0;

    for (uint32_t i = 0; i < buckets; i++) {
        double observed = (double)counts[i];
        double diff = observed - expected;
        chi2 += (diff * diff) / expected;
    }

    return chi2;
}

/**
 * Runs test for independence
 *
 * ALGORITHM:
 * 1. Generate sequence of N values
 * 2. Count "runs" (monotonic sequences)
 * 3. Compare with expected runs: (2N - 1) / 3
 * 4. Compute Z-score
 *
 * EXAMPLE:
 * Sequence: [3, 1, 4, 1, 5, 9, 2]
 * Runs: down(3→1), up(1→4→5→9), down(9→2) = 3 runs
 */
double lcg_test_runs(lcg_state_t *state, uint32_t samples)
{
    if (state == NULL || samples < 2) {
        return -1.0;
    }

    uint32_t runs = 1; /* Start with 1 run */
    uint32_t prev = lcg_next(state);

    for (uint32_t i = 1; i < samples; i++) {
        uint32_t curr = lcg_next(state);

        /* New run if direction changes */
        if ((curr > prev) != ((i > 0) && (lcg_get_state(state) > prev))) {
            runs++;
        }

        prev = curr;
    }

    /* Expected runs: (2n - 1) / 3 */
    double n = (double)samples;
    double expected = (2.0 * n - 1.0) / 3.0;

    /* Variance: (16n - 29) / 90 */
    double variance = (16.0 * n - 29.0) / 90.0;
    double stddev = sqrt(variance);

    /* Z-score: (observed - expected) / stddev */
    double z_score = ((double)runs - expected) / stddev;

    return z_score;
}

/*******************************************************************************
 * DEBUGGING / INTROSPECTION
 ******************************************************************************/

uint32_t lcg_get_state(const lcg_state_t *state)
{
    return state ? state->x : 0;
}

uint64_t lcg_get_count(const lcg_state_t *state)
{
    return state ? state->count : 0;
}

void lcg_reset(lcg_state_t *state, uint32_t seed)
{
    lcg_init(state, seed);
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Simulate coin flips
 */
void example_coin_flips(void)
{
    printf("\n=== Example: Coin Flips ===\n");
    printf("Flip a fair coin 100 times using LCG\n\n");

    lcg_state_t rng;
    lcg_init(&rng, 42); /* Deterministic seed */

    uint32_t heads = 0, tails = 0;

    for (int i = 0; i < 100; i++) {
        if (lcg_uniform(&rng) < 0.5) {
            heads++;
            if (i < 20) printf("H "); /* Print first 20 */
        } else {
            tails++;
            if (i < 20) printf("T ");
        }
    }

    printf("\n\nResults:\n");
    printf("  Heads: %u (%.1f%%)\n", heads, (heads * 100.0) / 100.0);
    printf("  Tails: %u (%.1f%%)\n", tails, (tails * 100.0) / 100.0);
    printf("  Expected: 50%% each\n");

    printf("===========================\n\n");
}

/**
 * Example: Lottery ticket selection
 */
void example_lottery_tickets(void)
{
    printf("\n=== Example: Lottery Ticket Selection ===\n");
    printf("3 tasks with different ticket counts:\n");
    printf("  Task A: 100 tickets\n");
    printf("  Task B: 200 tickets (2x A)\n");
    printf("  Task C: 50 tickets (0.5x A)\n\n");

    lcg_state_t rng;
    lcg_init(&rng, 12345);

    uint32_t total_tickets = 100 + 200 + 50; /* 350 */
    uint32_t wins[3] = {0}; /* A, B, C */

    /* Run lottery 1000 times */
    for (int i = 0; i < 1000; i++) {
        uint32_t ticket = lcg_range(&rng, total_tickets);

        if (ticket < 100) {
            wins[0]++; /* Task A wins */
        } else if (ticket < 300) {
            wins[1]++; /* Task B wins */
        } else {
            wins[2]++; /* Task C wins */
        }
    }

    printf("After 1000 lotteries:\n");
    printf("  Task A won: %u times (%.1f%%, expected 28.6%%)\n",
           wins[0], (wins[0] * 100.0) / 1000.0);
    printf("  Task B won: %u times (%.1f%%, expected 57.1%%)\n",
           wins[1], (wins[1] * 100.0) / 1000.0);
    printf("  Task C won: %u times (%.1f%%, expected 14.3%%)\n",
           wins[2], (wins[2] * 100.0) / 1000.0);

    printf("=========================================\n\n");
}

/**
 * Example: Statistical validation
 */
void example_statistical_tests(void)
{
    printf("\n=== Example: Statistical Tests ===\n");

    lcg_state_t rng;
    lcg_init(&rng, 99999);

    /* Chi-squared test */
    printf("Chi-squared test (uniformity):\n");
    double chi2 = lcg_test_uniform(&rng, 10, 10000);
    printf("  χ² statistic: %.2f\n", chi2);
    printf("  Critical value (α=0.05, df=9): 16.92\n");
    if (chi2 < 16.92) {
        printf("  Result: PASS (uniform distribution)\n");
    } else {
        printf("  Result: FAIL (non-uniform)\n");
    }

    /* Runs test */
    lcg_reset(&rng, 99999);
    printf("\nRuns test (independence):\n");
    double z = lcg_test_runs(&rng, 1000);
    printf("  Z-score: %.2f\n", z);
    printf("  Critical value (α=0.05): ±1.96\n");
    if (fabs(z) < 1.96) {
        printf("  Result: PASS (independent)\n");
    } else {
        printf("  Result: FAIL (correlated)\n");
    }

    printf("==================================\n\n");
}

/**
 * Run all LCG examples
 */
void lcg_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   LINEAR CONGRUENTIAL GENERATOR - EXAMPLES                 ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_coin_flips();
    example_lottery_tickets();
    example_statistical_tests();

    printf("All LCG examples completed.\n");
    printf("See include/lcg.h for API documentation.\n\n");
}
