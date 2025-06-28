#include "include/quaternion_spinlock.h"
#include "include/defs.h" // For panic (if used later)
#include <stdatomic.h>    // Ensure this is included for atomic operations
#include <string.h>       // For memset (optional, if used)

// Forward declarations for functions assumed to be defined elsewhere
struct cpu; // Already forward-declared in the header, but good for clarity
extern struct cpu* mycpu(void);
extern void getcallerpcs(void *v, uintptr_t pcs[]);
// extern void pushcli(void); // If we decide to use them for critical sections
// extern void popcli(void);

// Define a quaternion representing an "unlocked" or "no owner" state for current_owner_pos.
const quaternion_t QSPIN_NO_OWNER_POS = {0.0, 0.0, 0.0, 0.0};

// Pre-defined fairness rotation quaternion.
const quaternion_t DEFAULT_FAIRNESS_ROTATION = {0.996194698, 0.087155742, 0.0, 0.0}; // cos(5 deg), sin(5 deg), 0, 0

void qspin_lock_init(qspin_lock_t* lock, const char* name) {
    lock->name = name;
    atomic_store(&lock->locked_flag, 0); // 0 means unlocked
    lock->current_owner_pos = QSPIN_NO_OWNER_POS;
    lock->fairness_rot = DEFAULT_FAIRNESS_ROTATION;
    lock->cpu = 0; // Or NULL
    // Initialize pcs, e.g., by setting the first element to 0 or memset
    if (sizeof(lock->pcs) > 0) { // Check to avoid issues with zero-size arrays if pcs[0] was used
       // lock->pcs[0] = 0;
       memset(lock->pcs, 0, sizeof(lock->pcs)); // Safer option
    }
}

void qspin_lock(qspin_lock_t* lock, int cpu_id) {
    // Consider pushcli(); here if disabling interrupts is desired.
    // if (qspin_holding(lock)) {
    //     // Handle re-entrancy if necessary, or panic
    //     // For now, assume non-reentrant or panic in a higher level function if needed
    // }

    quaternion_t pos = quaternion_from_cpu_id(cpu_id);
    unsigned int expected_unlocked = 0;
    unsigned int desired_locked = 1;

    while (!atomic_compare_exchange_strong(&lock->locked_flag, &expected_unlocked, desired_locked)) {
        expected_unlocked = 0;
        pos = quaternion_multiply(pos, lock->fairness_rot);
        hyperbolic_pause(quaternion_norm(pos));
    }

    // Lock acquired successfully
    lock->current_owner_pos = pos;
    lock->cpu = mycpu();
    // The original xv6 used __builtin_frame_address(0) for the first argument.
    // It depends on how getcallerpcs is implemented.
    // Using `(void*)__builtin_frame_address(0)` is common for stack walking.
    getcallerpcs((void*)__builtin_frame_address(0), lock->pcs);

    // Consider __sync_synchronize(); memory barrier here.
}

void qspin_unlock(qspin_lock_t* lock) {
    // if (!qspin_holding(lock)) {
    //     // Panic or handle error: trying to unlock a lock not held by this CPU
    // }

    // Consider __sync_synchronize(); memory barrier here before releasing.

    // Clear debugging/ownership info before releasing the lock
    if (sizeof(lock->pcs) > 0) {
        // lock->pcs[0] = 0;
        memset(lock->pcs, 0, sizeof(lock->pcs)); // Safer option
    }
    lock->cpu = 0; // Or NULL
    lock->current_owner_pos = QSPIN_NO_OWNER_POS;

    atomic_store(&lock->locked_flag, 0); // Release the lock

    // Consider popcli(); if interrupts were disabled.
}

int qspin_holding(qspin_lock_t* lock) {
    // This check assumes that reading lock->locked_flag and lock->cpu
    // while potentially being modified by another CPU is acceptable for a 'holding' check.
    // For a robust check, especially if mycpu() itself could be complex or if
    // strict memory ordering is needed, one might need interrupt disabling or memory barriers.
    // However, for typical spinlock 'holding' checks, this is often sufficient.
    return lock->locked_flag && lock->cpu == mycpu();
}
