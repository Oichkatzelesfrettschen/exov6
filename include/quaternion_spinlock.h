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

void qspin_lock_init(qspin_lock_t* lock, const char* name); // New init function
void qspin_lock(qspin_lock_t* lock, int cpu_id); // Matches framework, cpu_id for fairness
void qspin_unlock(qspin_lock_t* lock);
int qspin_holding(qspin_lock_t* lock);
// int qspin_trylock(qspin_lock_t* lock, int cpu_id); // Optional: if we want a trylock

#endif // QUATERNION_SPINLOCK_H
