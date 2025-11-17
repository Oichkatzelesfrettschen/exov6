/**
 * @file lwkt_token.c
 * @brief LWKT (Light-Weight Kernel Thread) Token implementation
 *
 * Inspired by DragonFlyBSD's LWKT token design:
 * - CPU-owned soft locks
 * - Automatically released on context switch
 * - No sleep/wakeup - pure spin
 * - Extremely low overhead
 * - Perfect for exokernel capability traversal
 *
 * Key differences from traditional locks:
 * - Ownership tied to CPU, not thread
 * - Multiple tokens can be held per CPU
 * - Automatic release via token_release_all() in scheduler
 * - No blocking - spin until acquired
 * - Hash-based pool for distribution
 *
 * @version 1.0
 * @date 2025-11-17
 */

#include <types.h>
#include <string.h>
#include "defs.h"
#include "param.h"
#include "arch.h"
#include "memlayout.h"
#include "compiler_attrs.h"
#include "exo_lock.h"
#include "proc.h"

/* ========================================================================
 * Architecture-Specific Helpers
 * ======================================================================== */

/**
 * Read Time-Stamp Counter
 */
static inline uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

/* Note: pause() is defined in include/arch_x86_64.h */

/**
 * Compiler barrier
 */
static inline void barrier(void) {
    __asm__ __volatile__("" ::: "memory");
}

/* ========================================================================
 * Token Pool and Per-CPU Lists
 * ======================================================================== */

/**
 * Global token pool (hash-based distribution)
 */
struct lwkt_token token_pool[TOKEN_POOL_SIZE];

/**
 * Per-CPU token ownership lists
 */
struct cpu_token_list cpu_tokens[NCPU];

/* ========================================================================
 * Hash Function
 * ======================================================================== */

/**
 * Hash pointer to pool index
 *
 * Uses XOR folding for good distribution
 *
 * @param ptr Pointer to hash
 * @return Pool index (0 to TOKEN_POOL_SIZE-1)
 */
static EXO_ALWAYS_INLINE uint32_t hash_ptr(void *ptr) {
    uintptr_t val = (uintptr_t)ptr;

    // XOR fold to mix bits
    val = (val >> 6) ^ (val >> 12) ^ (val >> 18) ^ (val >> 24);

    // Mask to pool size
    return val & (TOKEN_POOL_SIZE - 1);
}

/* ========================================================================
 * Per-CPU Token List Management
 * ======================================================================== */

/**
 * Add token to CPU's ownership list
 *
 * @param cpu CPU ID
 * @param token Token to add
 */
static void cpu_token_add(uint32_t cpu, struct lwkt_token *token) {
    struct cpu_token_list *list = &cpu_tokens[cpu];

    if (unlikely(list->count >= MAX_TOKENS_PER_CPU)) {
        panic("cpu_token_add: too many tokens (max %d)", MAX_TOKENS_PER_CPU);
    }

    list->tokens[list->count++] = token;
}

/**
 * Remove token from CPU's ownership list
 *
 * @param cpu CPU ID
 * @param token Token to remove
 */
static void cpu_token_remove(uint32_t cpu, struct lwkt_token *token) {
    struct cpu_token_list *list = &cpu_tokens[cpu];

    // Find and remove token
    for (uint32_t i = 0; i < list->count; i++) {
        if (list->tokens[i] == token) {
            // Shift remaining tokens down
            for (uint32_t j = i; j < list->count - 1; j++) {
                list->tokens[j] = list->tokens[j + 1];
            }
            list->count--;
            return;
        }
    }

    panic("cpu_token_remove: token not found");
}

/* ========================================================================
 * Token Pool Initialization
 * ======================================================================== */

/**
 * Initialize token pool
 *
 * Called once at boot
 */
void token_pool_init(void) {
    // Initialize all pool tokens
    // Pool tokens typically protect capability tables (level 60)
    for (int i = 0; i < TOKEN_POOL_SIZE; i++) {
        token_init(&token_pool[i], "pool_token", LOCK_LEVEL_CAPABILITY);
        token_pool[i].hash = i;
    }

    // Initialize per-CPU token lists
    for (int i = 0; i < NCPU; i++) {
        cpu_tokens[i].count = 0;
        for (int j = 0; j < MAX_TOKENS_PER_CPU; j++) {
            cpu_tokens[i].tokens[j] = NULL;
        }
    }

    cprintf("lwkt_token: initialized pool with %d tokens, %d max per CPU\n",
            TOKEN_POOL_SIZE, MAX_TOKENS_PER_CPU);
}

/**
 * Get token from pool for a resource
 *
 * Maps resource pointer to a specific token via hash function
 *
 * @param resource Resource pointer (e.g., capability table)
 * @return Token to use for protecting this resource
 */
struct lwkt_token *token_pool_get(void *resource) {
    if (!resource) {
        panic("token_pool_get: NULL resource");
    }

    uint32_t hash = hash_ptr(resource);
    return &token_pool[hash];
}

/* ========================================================================
 * Token Operations
 * ======================================================================== */

/**
 * Initialize LWKT token
 *
 * @param token Token to initialize
 * @param name Debug name
 */
void token_init(struct lwkt_token *token, const char *name, uint32_t dag_level) {
    // Set to free (no owner)
    atomic_store_explicit(&token->owner_cpu, TOKEN_FREE_MARKER, memory_order_relaxed);

    // Metadata
    token->hash = hash_ptr(token);
    token->name = name;
    token->dag_level = dag_level;
    token->acquire_tsc = 0;

    // Zero statistics
    memset(&token->stats, 0, sizeof(token->stats));
}

/**
 * Acquire LWKT token
 *
 * Fast path: Already own it (reacquire)
 * Slow path: Spin until free, then acquire
 *
 * @param token Token to acquire
 */
void token_acquire(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;

    /* ===== FAST PATH: Already own it ===== */
    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);

    if (likely(owner == my_cpu)) {
        // We already own it - just increment reacquire count
        // No DAG check needed for reacquisition
        __sync_fetch_and_add(&token->stats.reacquire_count, 1);
        return;
    }

#ifdef USE_DAG_CHECKING
    // Validate DAG ordering before first acquisition
    // (not needed for reacquisition above)
    if (!dag_validate_acquisition(token, token->name, token->dag_level,
                                  LOCK_TYPE_TOKEN, __FILE__, __LINE__)) {
#ifdef DAG_PANIC_ON_VIOLATION
        panic("token_acquire: DAG violation");
#else
        return;  // Skip acquisition on violation (warning mode)
#endif
    }
#endif

    /* ===== SLOW PATH: Acquire from free or other CPU ===== */
    uint64_t spin_start = rdtsc();
    int backoff = 10;
    bool contended = false;

    while (1) {
        uint32_t expected = TOKEN_FREE_MARKER;

        // Try to acquire
        if (atomic_compare_exchange_strong_explicit(
                &token->owner_cpu, &expected, my_cpu,
                memory_order_acquire, memory_order_relaxed)) {
            // Acquired!

            // Record acquisition time
            token->acquire_tsc = rdtsc();

            // Update statistics
            __sync_fetch_and_add(&token->stats.acquire_count, 1);
            __sync_fetch_and_add(&token->stats.cpu_acquire_count[my_cpu], 1);

            if (contended) {
                __sync_fetch_and_add(&token->stats.contention_count, 1);
            }

            // Add to CPU's token list
            cpu_token_add(my_cpu, token);

#ifdef USE_DAG_CHECKING
            // Record acquisition in DAG tracker
            dag_lock_acquired(token, token->name, token->dag_level,
                             LOCK_TYPE_TOKEN, __FILE__, __LINE__);
#endif

            return;
        }

        // Failed - token is owned by another CPU
        contended = true;

        // Spin with exponential backoff
        for (int i = 0; i < backoff; i++) {
            pause();
        }

        backoff = (backoff < 1000) ? backoff * 2 : 1000;

        // Check if token is now free
        if (atomic_load_explicit(&token->owner_cpu, memory_order_relaxed) == TOKEN_FREE_MARKER) {
            // Retry immediately
            continue;
        }

        // Still owned - continue spinning
    }
}

/**
 * Release LWKT token
 *
 * Verifies ownership and releases token
 *
 * @param token Token to release
 */
void token_release(struct lwkt_token *token) {
#ifdef USE_DAG_CHECKING
    // Track lock release in DAG
    dag_lock_released(token);
#endif

    uint32_t my_cpu = mycpu() - cpus;

    // Verify we own it
    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);

    if (unlikely(owner != my_cpu)) {
        panic("token_release: not owner (owner=%u, my_cpu=%u, token=%s)",
              owner, my_cpu, token->name);
    }

    // Calculate hold time
    uint64_t hold_cycles = rdtsc() - token->acquire_tsc;

    // Update statistics
    __sync_fetch_and_add(&token->stats.release_count, 1);
    __sync_fetch_and_add(&token->stats.total_hold_cycles, hold_cycles);

    // Update max hold time (atomic max operation)
    uint64_t old_max = token->stats.max_hold_cycles;
    while (hold_cycles > old_max) {
        if (__sync_bool_compare_and_swap(&token->stats.max_hold_cycles,
                                         old_max, hold_cycles)) {
            break;
        }
        old_max = token->stats.max_hold_cycles;
    }

    // Remove from CPU's token list
    cpu_token_remove(my_cpu, token);

    // Release ownership
    atomic_store_explicit(&token->owner_cpu, TOKEN_FREE_MARKER, memory_order_release);
}

/**
 * Release all tokens held by current CPU
 *
 * CRITICAL: Called by scheduler before context switch!
 *
 * This is the key mechanism that makes tokens "soft locks":
 * - Tokens automatically released when thread blocks
 * - No need for manual release on every code path
 * - Prevents deadlocks from holding tokens across block
 */
void token_release_all(void) {
    uint32_t my_cpu = mycpu() - cpus;
    struct cpu_token_list *list = &cpu_tokens[my_cpu];

    // Release all tokens held by this CPU
    for (uint32_t i = 0; i < list->count; i++) {
        struct lwkt_token *token = list->tokens[i];

        // Calculate hold time
        uint64_t hold_cycles = rdtsc() - token->acquire_tsc;

        // Update statistics
        __sync_fetch_and_add(&token->stats.release_count, 1);
        __sync_fetch_and_add(&token->stats.total_hold_cycles, hold_cycles);

        // Update max hold time
        uint64_t old_max = token->stats.max_hold_cycles;
        while (hold_cycles > old_max) {
            if (__sync_bool_compare_and_swap(&token->stats.max_hold_cycles,
                                             old_max, hold_cycles)) {
                break;
            }
            old_max = token->stats.max_hold_cycles;
        }

        // Release ownership
        atomic_store_explicit(&token->owner_cpu, TOKEN_FREE_MARKER, memory_order_release);
    }

    // Clear token list
    list->count = 0;
}

/* ========================================================================
 * Verification and Debugging
 * ======================================================================== */

/**
 * Check if current CPU holds token
 *
 * @param token Token to check
 * @return 1 if holding, 0 otherwise
 */
int token_holding(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;
    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);
    return owner == my_cpu;
}

/**
 * Assert that current CPU holds token (panic if not)
 *
 * @param token Token to check
 */
void token_assert_held(struct lwkt_token *token) {
    if (!token_holding(token)) {
        uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);
        panic("token_assert_held: token '%s' not held (owner=%u)",
              token->name, owner);
    }
}

/* ========================================================================
 * Statistics and Debugging
 * ======================================================================== */

/**
 * Dump token statistics
 *
 * @param token Token to dump stats for
 * @param name Name to display (or NULL to use token->name)
 */
void token_dump_stats(struct lwkt_token *token, const char *name) {
    struct lwkt_token_stats *s = &token->stats;

    cprintf("\n=== LWKT Token Stats: %s ===\n", name ? name : token->name);
    cprintf("Acquisitions:\n");
    cprintf("  Total:           %lu\n", s->acquire_count);
    cprintf("  Reacquires:      %lu\n", s->reacquire_count);
    cprintf("  Releases:        %lu\n", s->release_count);

    if (s->contention_count > 0) {
        cprintf("\nContention:\n");
        cprintf("  Events:          %lu\n", s->contention_count);
        cprintf("  Rate:            %.1f%%\n",
                100.0 * s->contention_count / (s->acquire_count + 1));
    }

    if (s->acquire_count > 0) {
        cprintf("\nHold Time:\n");
        cprintf("  Avg cycles:      %lu\n",
                s->total_hold_cycles / s->acquire_count);
        cprintf("  Max cycles:      %lu\n", s->max_hold_cycles);
    }

    // Per-CPU acquisition breakdown
    cprintf("\nPer-CPU Acquisitions:\n");
    for (int i = 0; i < NCPU; i++) {
        if (s->cpu_acquire_count[i] > 0) {
            cprintf("  CPU %d:           %lu (%.1f%%)\n",
                    i, s->cpu_acquire_count[i],
                    100.0 * s->cpu_acquire_count[i] / (s->acquire_count + 1));
        }
    }

    // Current status
    uint32_t owner = atomic_load_explicit(&token->owner_cpu, memory_order_relaxed);
    cprintf("\nCurrent Status:\n");
    if (owner == TOKEN_FREE_MARKER) {
        cprintf("  State:           FREE\n");
    } else {
        cprintf("  State:           HELD by CPU %u\n", owner);
    }
}

/**
 * Reset token statistics
 *
 * @param token Token to reset stats for
 */
void token_reset_stats(struct lwkt_token *token) {
    memset(&token->stats, 0, sizeof(token->stats));
}
