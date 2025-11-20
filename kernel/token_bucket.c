/**
 * @file token_bucket.c
 * @brief Token Bucket Rate Limiting Algorithm
 *
 * This file implements the classic token bucket algorithm for rate limiting
 * capability accesses. Token buckets are used in network QoS, API rate limiting,
 * and resource scheduling.
 *
 * ALGORITHM OVERVIEW:
 * - Bucket holds tokens (up to capacity)
 * - Tokens refill at fixed rate
 * - Each access consumes tokens
 * - Access denied if insufficient tokens
 *
 * REAL-WORLD USAGE:
 * - AWS API Gateway rate limiting
 * - Linux traffic control (tc)
 * - Network QoS (Quality of Service)
 * - Database connection pooling
 *
 * PEDAGOGICAL NOTE:
 * Token bucket differs from leaky bucket:
 * - Token bucket: Allows bursts (up to capacity)
 * - Leaky bucket: Smooth rate (no bursts)
 *
 * @see include/capability_v2.h for token_bucket struct definition
 */

#include "capability_v2.h"
#include "printf.h"
#include <stdint.h>

/*******************************************************************************
 * HELPER FUNCTIONS
 ******************************************************************************/

/**
 * Get current timestamp (milliseconds)
 *
 * TODO: Integrate with platform timer
 */
static uint64_t get_current_time_ms(void)
{
    /* TODO: Use TSC, HPET, or other hardware timer */
    return 0; /* Placeholder */
}

/*******************************************************************************
 * TOKEN BUCKET CORE OPERATIONS
 ******************************************************************************/

/**
 * Initialize a token bucket
 *
 * @param bucket Token bucket to initialize
 * @param capacity Maximum tokens (burst size)
 * @param refill_rate Tokens added per second (Q16.16 fixed-point)
 *
 * PARAMETERS:
 * - capacity: Maximum burst size (e.g., 100 requests)
 * - refill_rate: Sustained rate (e.g., Q16(10) = 10 requests/sec)
 *
 * EXAMPLE:
 * ```c
 * struct token_bucket bucket;
 * token_bucket_init(&bucket, 100, Q16(10)); // 100 burst, 10/sec sustained
 * ```
 */
void token_bucket_init(struct token_bucket *bucket, q16_t capacity, q16_t refill_rate)
{
    if (bucket == NULL) {
        return;
    }

    bucket->capacity = capacity;
    bucket->tokens = capacity; /* Start with full bucket */
    bucket->refill_rate = refill_rate;
    bucket->last_refill = get_current_time_ms();
}

/**
 * Refill tokens based on elapsed time
 *
 * @param bucket Token bucket to refill
 *
 * ALGORITHM:
 * 1. Calculate elapsed time since last refill
 * 2. Calculate tokens to add: (elapsed_ms / 1000) * refill_rate
 * 3. Add tokens (capped at capacity)
 * 4. Update last_refill timestamp
 *
 * TIME COMPLEXITY: O(1)
 *
 * FIXED-POINT ARITHMETIC:
 * - refill_rate is in tokens/second (Q16.16)
 * - elapsed_time is in milliseconds
 * - Conversion: tokens = (refill_rate * elapsed_ms) / 1000
 */
static void token_bucket_refill(struct token_bucket *bucket)
{
    if (bucket == NULL) {
        return;
    }

    uint64_t current_time = get_current_time_ms();
    uint64_t elapsed_ms = current_time - bucket->last_refill;

    if (elapsed_ms == 0) {
        return; /* No time elapsed */
    }

    /* Calculate tokens to add (fixed-point arithmetic) */
    /* tokens_to_add = (refill_rate * elapsed_ms) / 1000 */
    /* Note: refill_rate is Q16.16, so multiply by elapsed_ms first, then divide by 1000 */
    uint64_t tokens_to_add_q16 = ((uint64_t)bucket->refill_rate * elapsed_ms) / 1000;
    q16_t tokens_to_add = (q16_t)tokens_to_add_q16;

    /* Add tokens (capped at capacity) */
    bucket->tokens += tokens_to_add;
    if (bucket->tokens > bucket->capacity) {
        bucket->tokens = bucket->capacity;
    }

    /* Update last refill time */
    bucket->last_refill = current_time;
}

/**
 * Consume tokens from bucket
 *
 * @param bucket Token bucket
 * @param tokens_needed Number of tokens to consume (Q16.16 fixed-point)
 * @return 1 if sufficient tokens (access granted), 0 if insufficient (rate limited)
 *
 * ALGORITHM:
 * 1. Refill bucket based on elapsed time
 * 2. Check if sufficient tokens available
 * 3. If yes: consume tokens and return 1
 * 4. If no: return 0 (rate limited)
 *
 * EXAMPLE:
 * ```c
 * if (token_bucket_consume(&bucket, Q16(1))) {
 *     // Access granted
 *     perform_operation();
 * } else {
 *     // Rate limited
 *     return -EAGAIN;
 * }
 * ```
 */
int token_bucket_consume(struct token_bucket *bucket, q16_t tokens_needed)
{
    if (bucket == NULL) {
        return 0; /* Invalid bucket: deny access */
    }

    /* Refill tokens based on elapsed time */
    token_bucket_refill(bucket);

    /* Check if sufficient tokens available */
    if (bucket->tokens >= tokens_needed) {
        /* Consume tokens */
        bucket->tokens -= tokens_needed;
        return 1; /* Access granted */
    } else {
        /* Insufficient tokens */
        return 0; /* Rate limited */
    }
}

/**
 * Check if tokens available without consuming
 *
 * @param bucket Token bucket
 * @param tokens_needed Number of tokens to check
 * @return 1 if sufficient tokens, 0 otherwise
 *
 * USAGE: Dry-run check before actual consumption
 */
int token_bucket_check(struct token_bucket *bucket, q16_t tokens_needed)
{
    if (bucket == NULL) {
        return 0;
    }

    /* Refill tokens (updates bucket state) */
    token_bucket_refill(bucket);

    return (bucket->tokens >= tokens_needed) ? 1 : 0;
}

/**
 * Get current token count
 *
 * @param bucket Token bucket
 * @return Current number of tokens (Q16.16 fixed-point)
 *
 * USAGE: Monitoring and debugging
 */
q16_t token_bucket_get_tokens(struct token_bucket *bucket)
{
    if (bucket == NULL) {
        return 0;
    }

    /* Refill before reporting */
    token_bucket_refill(bucket);

    return bucket->tokens;
}

/**
 * Reset token bucket to full capacity
 *
 * @param bucket Token bucket to reset
 *
 * USAGE: Manual override, testing, or policy change
 */
void token_bucket_reset(struct token_bucket *bucket)
{
    if (bucket == NULL) {
        return;
    }

    bucket->tokens = bucket->capacity;
    bucket->last_refill = get_current_time_ms();
}

/**
 * Set new rate limit parameters
 *
 * @param bucket Token bucket
 * @param new_capacity New burst capacity
 * @param new_refill_rate New refill rate (tokens/sec)
 *
 * USAGE: Dynamic rate adjustment based on system load
 */
void token_bucket_set_params(struct token_bucket *bucket, q16_t new_capacity, q16_t new_refill_rate)
{
    if (bucket == NULL) {
        return;
    }

    /* Refill with old parameters first */
    token_bucket_refill(bucket);

    /* Update parameters */
    bucket->capacity = new_capacity;
    bucket->refill_rate = new_refill_rate;

    /* Cap current tokens at new capacity */
    if (bucket->tokens > bucket->capacity) {
        bucket->tokens = bucket->capacity;
    }
}

/*******************************************************************************
 * ADVANCED TOKEN BUCKET OPERATIONS
 ******************************************************************************/

/**
 * Stochastic token refill (PDAC innovation)
 *
 * @param bucket Token bucket
 * @param probability Probability of refill (Q16.16, range 0.0 to 1.0)
 *
 * PDAC ENHANCEMENT:
 * Instead of deterministic refill, refill tokens probabilistically.
 * This introduces fairness in multi-tenant systems where exact timing
 * is unpredictable (e.g., cloud environments with CPU sharing).
 *
 * ALGORITHM:
 * 1. Generate random number in [0, 1)
 * 2. If random < probability, refill normally
 * 3. Otherwise, skip refill
 *
 * USE CASE:
 * - Fair scheduling under CPU contention
 * - Probabilistic QoS guarantees
 * - Lottery scheduling integration
 *
 * EXAMPLE:
 * ```c
 * // 80% probability of refill (compensates for CPU stealing)
 * token_bucket_stochastic_refill(&bucket, Q16(0.8));
 * ```
 */
void token_bucket_stochastic_refill(struct token_bucket *bucket, q16_t probability)
{
    if (bucket == NULL) {
        return;
    }

    /* TODO: Integrate with kernel PRNG */
    /* For now, always refill (deterministic fallback) */
    (void)probability;
    token_bucket_refill(bucket);
}

/**
 * Hierarchical token bucket (HTB) - parent-child relationship
 *
 * @param child_bucket Child token bucket
 * @param parent_bucket Parent token bucket
 * @param tokens_needed Tokens to consume
 * @return 1 if both child and parent have sufficient tokens, 0 otherwise
 *
 * HIERARCHICAL RATE LIMITING:
 * - Child can consume tokens only if parent also has tokens
 * - Used for nested quotas (e.g., per-user inside per-tenant limit)
 * - Linux tc uses HTB for traffic shaping
 *
 * EXAMPLE:
 * ```c
 * // Tenant has 1000 req/s, user has 100 req/s
 * struct token_bucket tenant_bucket;
 * struct token_bucket user_bucket;
 * token_bucket_init(&tenant_bucket, 1000, Q16(1000));
 * token_bucket_init(&user_bucket, 100, Q16(100));
 *
 * if (token_bucket_htb_consume(&user_bucket, &tenant_bucket, Q16(1))) {
 *     // Both user and tenant have quota
 * }
 * ```
 */
int token_bucket_htb_consume(struct token_bucket *child_bucket,
                              struct token_bucket *parent_bucket,
                              q16_t tokens_needed)
{
    if (child_bucket == NULL || parent_bucket == NULL) {
        return 0;
    }

    /* Refill both buckets */
    token_bucket_refill(child_bucket);
    token_bucket_refill(parent_bucket);

    /* Check if both have sufficient tokens */
    if (child_bucket->tokens >= tokens_needed &&
        parent_bucket->tokens >= tokens_needed) {
        /* Consume from both */
        child_bucket->tokens -= tokens_needed;
        parent_bucket->tokens -= tokens_needed;
        return 1; /* Access granted */
    } else {
        return 0; /* Rate limited (by child or parent) */
    }
}

/*******************************************************************************
 * DEBUGGING AND INTROSPECTION
 ******************************************************************************/

/**
 * Print token bucket state
 *
 * @param bucket Token bucket to print
 * @param name Descriptive name for debugging
 */
void token_bucket_print(struct token_bucket *bucket, const char *name)
{
    if (bucket == NULL) {
        printf("Token bucket '%s': NULL\n", name ? name : "unknown");
        return;
    }

    /* Refill before printing */
    token_bucket_refill(bucket);

    printf("=== Token Bucket: %s ===\n", name ? name : "unknown");
    printf("Capacity:     %d (Q16.16)\n", bucket->capacity);
    printf("Current:      %d (Q16.16) = %.2f tokens\n",
           bucket->tokens, Q16_TO_FLOAT(bucket->tokens));
    printf("Refill Rate:  %d (Q16.16) = %.2f tokens/sec\n",
           bucket->refill_rate, Q16_TO_FLOAT(bucket->refill_rate));
    printf("Last Refill:  %lu ms\n", bucket->last_refill);
    printf("Utilization:  %.1f%%\n",
           (Q16_TO_FLOAT(bucket->tokens) * 100.0) / Q16_TO_FLOAT(bucket->capacity));
    printf("==========================\n");
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Basic token bucket rate limiting
 *
 * DEMONSTRATES: Simple rate limiting with bursts
 */
void example_token_bucket_basic(void)
{
    printf("\n=== Example: Basic Token Bucket ===\n");
    printf("Scenario: 10 requests/sec sustained, 50 burst capacity\n\n");

    struct token_bucket bucket;
    token_bucket_init(&bucket, Q16(50), Q16(10)); /* 50 burst, 10/sec */

    printf("Initial state:\n");
    token_bucket_print(&bucket, "API Rate Limiter");

    /* Simulate burst of 50 requests */
    printf("\nBurst of 50 requests:\n");
    for (int i = 0; i < 50; i++) {
        if (token_bucket_consume(&bucket, Q16(1))) {
            /* Request granted */
        } else {
            printf("Request %d: RATE LIMITED\n", i + 1);
            break;
        }
    }

    printf("\nAfter burst:\n");
    token_bucket_print(&bucket, "API Rate Limiter");

    /* Try one more request (should fail) */
    printf("\nOne more request:\n");
    if (token_bucket_consume(&bucket, Q16(1))) {
        printf("Request granted\n");
    } else {
        printf("Request RATE LIMITED (bucket empty)\n");
    }

    printf("===================================\n\n");
}

/**
 * Example: Hierarchical token buckets (HTB)
 *
 * DEMONSTRATES: Nested rate limits (tenant > user)
 */
void example_token_bucket_hierarchical(void)
{
    printf("\n=== Example: Hierarchical Token Buckets ===\n");
    printf("Scenario: Tenant limit 1000/sec, User limit 100/sec\n\n");

    struct token_bucket tenant_bucket;
    struct token_bucket user_bucket;

    token_bucket_init(&tenant_bucket, Q16(1000), Q16(1000));
    token_bucket_init(&user_bucket, Q16(100), Q16(100));

    printf("Tenant bucket:\n");
    token_bucket_print(&tenant_bucket, "Tenant");

    printf("\nUser bucket:\n");
    token_bucket_print(&user_bucket, "User");

    /* Consume 100 requests (user limit) */
    printf("\nConsuming 100 requests:\n");
    int granted = 0;
    for (int i = 0; i < 100; i++) {
        if (token_bucket_htb_consume(&user_bucket, &tenant_bucket, Q16(1))) {
            granted++;
        }
    }
    printf("Granted: %d requests\n", granted);

    printf("\nAfter consumption:\n");
    token_bucket_print(&user_bucket, "User");
    token_bucket_print(&tenant_bucket, "Tenant");

    printf("==========================================\n\n");
}

/**
 * Run all token bucket examples
 */
void token_bucket_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   TOKEN BUCKET RATE LIMITING - PEDAGOGICAL EXAMPLES        ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_token_bucket_basic();
    example_token_bucket_hierarchical();

    printf("All token bucket examples completed.\n\n");
}
