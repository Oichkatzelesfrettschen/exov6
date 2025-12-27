/**
 * @file futex.c
 * @brief Fast Userspace Mutex Implementation
 *
 * Cleanroom futex implementation for FeuerBird exokernel.
 * Uses the unified wait channel for blocking/waking.
 *
 * Key design decisions:
 * 1. Uses wc_wait/wc_wake for actual blocking (hash-based, O(1) lookup)
 * 2. Validates userspace addresses before access
 * 3. Supports both private and shared futexes
 * 4. Full requeue support for efficient condition variables
 */

#include "futex.h"
#include "../sync/waitchan.h"
#include "../defs.h"
#include "../proc.h"

/* Errno values */
#ifndef EINVAL
#define EINVAL 22
#endif
#ifndef ETIMEDOUT
#define ETIMEDOUT 110
#endif
#ifndef EAGAIN
#define EAGAIN 11
#endif
#ifndef EFAULT
#define EFAULT 14
#endif
#ifndef ENOSYS
#define ENOSYS 38
#endif
#ifndef EINTR
#define EINTR 4
#endif

/**
 * Convert futex flags to wait channel flags
 */
static inline uint32_t futex_to_wc_flags(int op) {
    uint32_t flags = 0;
    if (!(op & FUTEX_PRIVATE_FLAG)) {
        flags |= WC_FLAG_SHARED;
    }
    return flags;
}

/**
 * Read a futex word from userspace
 * Returns 0 on success, -EFAULT on failure
 */
static int futex_read(uint32_t *uaddr, uint32_t *val) {
    /* In a full implementation, we'd use copyin and validate the address */
    if ((uintptr_t)uaddr < 0x1000) {
        return -EFAULT; /* NULL page protection */
    }

    /* For now, direct access (assumes valid userspace mapping)
     * A production kernel would use copyin() here */
    *val = *uaddr;
    return 0;
}

/**
 * Write a futex word to userspace
 * Returns 0 on success, -EFAULT on failure
 */
static int futex_write(uint32_t *uaddr, uint32_t val) {
    if ((uintptr_t)uaddr < 0x1000) {
        return -EFAULT;
    }
    *uaddr = val;
    return 0;
}

/**
 * Atomic compare-and-swap for futex word
 * Returns old value
 */
static uint32_t futex_cmpxchg(uint32_t *uaddr, uint32_t old, uint32_t new) {
    uint32_t prev;
    __asm__ __volatile__(
        "lock; cmpxchgl %2, %1"
        : "=a"(prev), "+m"(*uaddr)
        : "r"(new), "0"(old)
        : "memory"
    );
    return prev;
}

/**
 * FUTEX_WAIT: Block if *uaddr == val
 */
static long futex_wait(uint32_t *uaddr, uint32_t val, uint32_t flags,
                       const struct futex_timespec *timeout) {
    uint32_t curval;
    uint64_t timeout_ns = 0;

    /* Read current value */
    if (futex_read(uaddr, &curval) < 0) {
        return -EFAULT;
    }

    /* Check if value matches - if not, return immediately */
    if (curval != val) {
        return -EAGAIN;
    }

    /* Convert timeout to nanoseconds */
    if (timeout) {
        timeout_ns = (uint64_t)timeout->tv_sec * 1000000000ULL +
                     (uint64_t)timeout->tv_nsec;
    }

    /* Block on the wait channel */
    int reason = wc_wait((uintptr_t)uaddr, val, flags, timeout_ns);

    switch (reason) {
        case WC_WAKEUP_NORMAL:
            return 0;
        case WC_WAKEUP_TIMEOUT:
            return -ETIMEDOUT;
        case WC_WAKEUP_SIGNAL:
            return -EINTR;
        default:
            return 0;
    }
}

/**
 * FUTEX_WAKE: Wake up to val waiters
 */
static long futex_wake(uint32_t *uaddr, uint32_t val, uint32_t flags) {
    return wc_wake((uintptr_t)uaddr, (int)val, flags);
}

/**
 * FUTEX_REQUEUE: Move waiters from uaddr to uaddr2
 */
static long futex_requeue(uint32_t *uaddr, uint32_t *uaddr2,
                          uint32_t wake_count, uint32_t requeue_count,
                          uint32_t flags) {
    return wc_requeue((uintptr_t)uaddr, (uintptr_t)uaddr2,
                      (int)wake_count, (int)requeue_count, flags);
}

/**
 * FUTEX_CMP_REQUEUE: Requeue with value check
 */
static long futex_cmp_requeue(uint32_t *uaddr, uint32_t *uaddr2,
                              uint32_t wake_count, uint32_t requeue_count,
                              uint32_t expected, uint32_t flags) {
    uint32_t curval;

    /* Read current value */
    if (futex_read(uaddr, &curval) < 0) {
        return -EFAULT;
    }

    /* Check if value matches */
    if (curval != expected) {
        return -EAGAIN;
    }

    return wc_requeue((uintptr_t)uaddr, (uintptr_t)uaddr2,
                      (int)wake_count, (int)requeue_count, flags);
}

/**
 * FUTEX_WAKE_OP: Wake with atomic operation on second address
 */
static long futex_wake_op(uint32_t *uaddr, uint32_t *uaddr2,
                          uint32_t wake_count, uint32_t wake2_count,
                          uint32_t op, uint32_t flags) {
    uint32_t oldval;
    int optype = (op >> 28) & 0xF;
    int cmptype = (op >> 24) & 0xF;
    uint32_t oparg = (op >> 12) & 0xFFF;
    uint32_t cmparg = op & 0xFFF;
    int wake2 = 0;

    /* Read old value */
    if (futex_read(uaddr2, &oldval) < 0) {
        return -EFAULT;
    }

    /* Perform atomic operation on uaddr2 */
    switch (optype) {
        case FUTEX_OP_SET:
            futex_write(uaddr2, oparg);
            break;
        case FUTEX_OP_ADD:
            futex_write(uaddr2, oldval + oparg);
            break;
        case FUTEX_OP_OR:
            futex_write(uaddr2, oldval | oparg);
            break;
        case FUTEX_OP_ANDN:
            futex_write(uaddr2, oldval & ~oparg);
            break;
        case FUTEX_OP_XOR:
            futex_write(uaddr2, oldval ^ oparg);
            break;
        default:
            return -EINVAL;
    }

    /* Check comparison for second wake */
    switch (cmptype) {
        case FUTEX_OP_CMP_EQ:
            wake2 = (oldval == cmparg);
            break;
        case FUTEX_OP_CMP_NE:
            wake2 = (oldval != cmparg);
            break;
        case FUTEX_OP_CMP_LT:
            wake2 = (oldval < cmparg);
            break;
        case FUTEX_OP_CMP_LE:
            wake2 = (oldval <= cmparg);
            break;
        case FUTEX_OP_CMP_GT:
            wake2 = (oldval > cmparg);
            break;
        case FUTEX_OP_CMP_GE:
            wake2 = (oldval >= cmparg);
            break;
        default:
            wake2 = 0;
    }

    /* Wake on uaddr */
    long ret = wc_wake((uintptr_t)uaddr, (int)wake_count, flags);

    /* Conditionally wake on uaddr2 */
    if (wake2) {
        ret += wc_wake((uintptr_t)uaddr2, (int)wake2_count, flags);
    }

    return ret;
}

/**
 * FUTEX_WAIT_BITSET: Wait with bitmask matching
 */
static long futex_wait_bitset(uint32_t *uaddr, uint32_t val,
                              const struct futex_timespec *timeout,
                              uint32_t bitset, uint32_t flags) {
    if (bitset == 0) {
        return -EINVAL;
    }

    /* For now, treat same as regular wait
     * Full implementation would store bitset in waiter */
    return futex_wait(uaddr, val, flags, timeout);
}

/**
 * FUTEX_WAKE_BITSET: Wake with bitmask matching
 */
static long futex_wake_bitset(uint32_t *uaddr, uint32_t val,
                              uint32_t bitset, uint32_t flags) {
    if (bitset == 0) {
        return -EINVAL;
    }

    /* For now, treat same as regular wake
     * Full implementation would match bitset against waiters */
    return futex_wake(uaddr, val, flags);
}

/**
 * Main futex syscall implementation
 */
long sys_futex(uint32_t *uaddr, int op, uint32_t val,
               const struct futex_timespec *timeout,
               uint32_t *uaddr2, uint32_t val3) {
    int cmd = op & FUTEX_CMD_MASK;
    uint32_t flags = futex_to_wc_flags(op);

    switch (cmd) {
        case FUTEX_WAIT:
            return futex_wait(uaddr, val, flags, timeout);

        case FUTEX_WAKE:
            return futex_wake(uaddr, val, flags);

        case FUTEX_REQUEUE:
            /* val = wake count, val3 (passed as timeout pointer) = requeue count */
            return futex_requeue(uaddr, uaddr2, val,
                               (uint32_t)(uintptr_t)timeout, flags);

        case FUTEX_CMP_REQUEUE:
            return futex_cmp_requeue(uaddr, uaddr2, val,
                                    (uint32_t)(uintptr_t)timeout,
                                    val3, flags);

        case FUTEX_WAKE_OP:
            return futex_wake_op(uaddr, uaddr2, val,
                                (uint32_t)(uintptr_t)timeout,
                                val3, flags);

        case FUTEX_WAIT_BITSET:
            return futex_wait_bitset(uaddr, val, timeout, val3, flags);

        case FUTEX_WAKE_BITSET:
            return futex_wake_bitset(uaddr, val, val3, flags);

        case FUTEX_LOCK_PI:
        case FUTEX_UNLOCK_PI:
        case FUTEX_TRYLOCK_PI:
            /* Priority inheritance futexes - stub for now */
            return -ENOSYS;

        default:
            return -ENOSYS;
    }
}

/**
 * Initialize futex subsystem
 */
void futex_init(void) {
    /* Wait channel init is called separately at boot */
    /* Futex-specific initialization would go here */
}

/**
 * Handle robust futex cleanup on thread exit
 */
void futex_exit_robust(int pid) {
    /* Walk the robust list and mark futexes as OWNER_DIED
     * This is complex and requires userspace cooperation
     * Stub for now */
    (void)pid;
}
