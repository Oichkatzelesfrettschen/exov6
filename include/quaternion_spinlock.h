#pragma once

#ifndef QUATERNION_SPINLOCK_H
#define QUATERNION_SPINLOCK_H

#include "octonion.h" // For quaternion_t (which handles atomics)
#include "kernel_compat.h"
#include <stdint.h> // For uintptr_t

struct cpu; // Forward declaration

// As per framework document Section 5.1
typedef struct {
    _Atomic unsigned int locked_flag; // 0 for unlocked, 1 for locked
    quaternion_t current_owner_pos;   // Stores the 'pos' of the CPU holding the lock
    quaternion_t fairness_rot;        // Fairness rotation
    const char *name;                // Name of the lock for debugging
    uintptr_t pcs[10];               // Call stack of the acquirer
    struct cpu *cpu;                 // CPU holding the lock
} qspin_lock_t;

/* Alias for compatibility */
typedef qspin_lock_t quaternion_spinlock_t;

/* Quaternion-based spinlock functions (renamed to avoid exo_lock.h qspin_* conflicts) */
void quat_lock_init(qspin_lock_t* lock, const char* name);
void quat_lock(qspin_lock_t* lock, int cpu_id);
void quat_unlock(qspin_lock_t* lock);
int quat_holding(qspin_lock_t* lock);

#endif // QUATERNION_SPINLOCK_H
