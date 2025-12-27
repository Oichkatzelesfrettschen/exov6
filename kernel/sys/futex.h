/**
 * @file futex.h
 * @brief Fast Userspace Mutex (futex) Interface
 *
 * Cleanroom implementation of futex for FeuerBird exokernel.
 * Provides the foundation for userspace synchronization primitives:
 * - pthread_mutex
 * - pthread_cond
 * - sem_wait/sem_post
 * - barriers
 *
 * Compatible with Linux futex ABI for binary compatibility.
 */
#pragma once

#include <stdint.h>

/**
 * Futex operations (compatible with Linux ABI)
 */
#define FUTEX_WAIT              0   /* Block if *uaddr == val */
#define FUTEX_WAKE              1   /* Wake up to val waiters */
#define FUTEX_FD                2   /* (deprecated) */
#define FUTEX_REQUEUE           3   /* Requeue waiters to uaddr2 */
#define FUTEX_CMP_REQUEUE       4   /* Conditional requeue */
#define FUTEX_WAKE_OP           5   /* Wake with atomic op */
#define FUTEX_LOCK_PI           6   /* Priority inheritance lock */
#define FUTEX_UNLOCK_PI         7   /* Priority inheritance unlock */
#define FUTEX_TRYLOCK_PI        8   /* Try PI lock */
#define FUTEX_WAIT_BITSET       9   /* Wait with bitmask */
#define FUTEX_WAKE_BITSET       10  /* Wake with bitmask */
#define FUTEX_WAIT_REQUEUE_PI   11  /* Wait + requeue with PI */
#define FUTEX_CMP_REQUEUE_PI    12  /* Compare + requeue with PI */

/**
 * Futex flags (ORed with operation)
 */
#define FUTEX_PRIVATE_FLAG      128 /* Use process-private futex */
#define FUTEX_CLOCK_REALTIME    256 /* Use CLOCK_REALTIME for timeout */

/**
 * Operation mask (strip flags)
 */
#define FUTEX_CMD_MASK          (~(FUTEX_PRIVATE_FLAG | FUTEX_CLOCK_REALTIME))

/**
 * Bitset for FUTEX_WAIT_BITSET / FUTEX_WAKE_BITSET
 * FUTEX_BITSET_MATCH_ANY wakes all waiters regardless of bitset
 */
#define FUTEX_BITSET_MATCH_ANY  0xFFFFFFFF

/**
 * Robust futex constants
 */
#define FUTEX_OWNER_DIED        0x40000000
#define FUTEX_WAITERS           0x80000000
#define FUTEX_TID_MASK          0x3FFFFFFF

/**
 * Wake operation for FUTEX_WAKE_OP
 */
#define FUTEX_OP_SET            0   /* *uaddr2 = oparg */
#define FUTEX_OP_ADD            1   /* *uaddr2 += oparg */
#define FUTEX_OP_OR             2   /* *uaddr2 |= oparg */
#define FUTEX_OP_ANDN           3   /* *uaddr2 &= ~oparg */
#define FUTEX_OP_XOR            4   /* *uaddr2 ^= oparg */

/**
 * Comparison operations for FUTEX_WAKE_OP
 */
#define FUTEX_OP_CMP_EQ         0   /* oldval == cmparg */
#define FUTEX_OP_CMP_NE         1   /* oldval != cmparg */
#define FUTEX_OP_CMP_LT         2   /* oldval < cmparg */
#define FUTEX_OP_CMP_LE         3   /* oldval <= cmparg */
#define FUTEX_OP_CMP_GT         4   /* oldval > cmparg */
#define FUTEX_OP_CMP_GE         5   /* oldval >= cmparg */

/**
 * Encode FUTEX_WAKE_OP operation
 */
#define FUTEX_OP(op, oparg, cmp, cmparg) \
    (((op) << 28) | ((cmp) << 24) | ((oparg) << 12) | (cmparg))

/**
 * Timespec structure for futex timeouts
 */
struct futex_timespec {
    int64_t tv_sec;
    int64_t tv_nsec;
};

/**
 * Main futex syscall
 *
 * @param uaddr     Userspace address of futex word
 * @param op        Operation (FUTEX_WAIT, FUTEX_WAKE, etc.)
 * @param val       Value argument (meaning depends on op)
 * @param timeout   Timeout for FUTEX_WAIT (can be NULL)
 * @param uaddr2    Second userspace address (for REQUEUE)
 * @param val3      Third value (for CMP_REQUEUE)
 * @return          Operation-specific return value, or -errno
 */
long sys_futex(uint32_t *uaddr, int op, uint32_t val,
               const struct futex_timespec *timeout,
               uint32_t *uaddr2, uint32_t val3);

/**
 * Initialize futex subsystem
 * Called once at boot after wc_init()
 */
void futex_init(void);

/**
 * Handle robust futex cleanup on thread exit
 * Called when a thread/process exits with held futexes
 *
 * @param pid   PID of exiting process
 */
void futex_exit_robust(int pid);
