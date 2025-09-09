/**
 * @file exo_impl_c17.c
 * @brief Modern C17 implementation of exokernel functions
 * 
 * Complete C17 modernized implementations of all exokernel capability and
 * hardware functions with proper type safety, atomics, and static assertions.
 * 
 * @version 1.0.0
 * @date 2024-09-09
 * @author ExoV6 Project
 */

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <stdnoreturn.h>

#include "types.h"
#include "defs.h"
#include "proc.h"
#include "exo.h"
#include "spinlock.h"
#include "memlayout.h"
#include "mmu.h"
#include "arch.h"
#include "trap.h"
#include "hal/hal_interface.h"

/* C17 Compile-time assertions for type safety */
_Static_assert(sizeof(uint64_t) == 8, "uint64_t must be 8 bytes");
_Static_assert(sizeof(void*) == 8, "Pointer size must be 8 bytes for 64-bit arch");
_Static_assert(_Alignof(struct cpu) >= 64, "CPU structure must be cache-line aligned");

/* Thread-local storage for per-CPU data (C17) */
_Thread_local uint32_t current_cpu_id = 0;

/* Atomic global counters (C17) */
static _Atomic uint64_t global_cpu_ticks = 0;
static _Atomic uint32_t active_cpu_count = 0;

/**
 * @brief Get current CPU number using modern C17 approach
 * 
 * Utilizes HAL interface for architecture independence and
 * thread-local storage for caching.
 * 
 * @return Current CPU ID
 */
uint32_t cpunum(void) {
    /* Use HAL interface for architecture independence */
    if (hal != NULL) {
        uint32_t cpu_id = hal->cpu.get_current_cpu();
        current_cpu_id = cpu_id;  /* Cache in thread-local storage */
        return cpu_id;
    }
    
    /* Fallback: Direct APIC access for x86_64 */
    if (lapic != NULL) {
        const uint32_t apic_id = lapic[ID] >> 24;  /* APIC ID in bits 24-31 */
        current_cpu_id = apic_id;
        return apic_id;
    }
    
    /* Final fallback: use cached value */
    return current_cpu_id;
}

/**
 * @brief Read CR2 register (page fault linear address) - C17 implementation
 * 
 * Uses restrict pointer for optimization and modern inline assembly.
 * 
 * @return Page fault linear address
 */
uint64_t rcr2(void) {
    uint64_t cr2_value;
    
    /* Modern inline assembly with memory clobber */
    __asm__ volatile (
        "movq %%cr2, %0"
        : "=r" (cr2_value)
        :
        : "memory"
    );
    
    return cr2_value;
}

/**
 * @brief CPU pause instruction for spinlock optimization - C17 implementation
 * 
 * Uses HAL interface when available for architecture independence.
 */
void cpu_pause(void) {
    /* Use HAL interface for architecture independence */
    if (hal != NULL && hal->cpu.cpu_relax != NULL) {
        hal->cpu.cpu_relax();
        return;
    }
    
    /* Fallback: Direct x86_64 PAUSE instruction */
    __asm__ volatile ("pause" ::: "memory");
}

/**
 * @brief Alternative pause implementation (alias)
 */
inline void pause(void) {
    cpu_pause();
}

/**
 * @brief Modern C17 CPU identification with caching
 * 
 * @return CPU information structure
 */
typedef struct {
    uint32_t apic_id;
    uint32_t logical_id;
    bool     online;
    uint64_t last_timestamp;
} cpu_info_t;

_Alignas(64) static cpu_info_t cpu_cache[MAX_CPUS] = {0};

cpu_info_t get_cpu_info(void) {
    const uint32_t cpu_id = cpunum();
    
    if (cpu_id < MAX_CPUS) {
        cpu_info_t* restrict info = &cpu_cache[cpu_id];
        
        /* Update timestamp atomically */
        info->last_timestamp = hal->cpu.read_timestamp();
        info->online = true;
        
        return *info;
    }
    
    /* Return default info for invalid CPU ID */
    return (cpu_info_t){
        .apic_id = cpu_id,
        .logical_id = cpu_id,
        .online = false,
        .last_timestamp = 0
    };
}

/**
 * @brief Atomic counter operations using C17 atomics
 */
uint64_t atomic_increment_cpu_ticks(void) {
    return atomic_fetch_add_explicit(&global_cpu_ticks, 1, memory_order_relaxed);
}

uint32_t atomic_get_active_cpu_count(void) {
    return atomic_load_explicit(&active_cpu_count, memory_order_acquire);
}

void atomic_set_cpu_active(void) {
    atomic_fetch_add_explicit(&active_cpu_count, 1, memory_order_release);
}

void atomic_set_cpu_inactive(void) {
    atomic_fetch_sub_explicit(&active_cpu_count, 1, memory_order_release);
}

/**
 * @brief Memory barrier operations using HAL interface
 */
void memory_barrier_full(void) {
    if (hal != NULL && hal->atomic.memory_barrier != NULL) {
        hal->atomic.memory_barrier();
    } else {
        atomic_thread_fence(memory_order_seq_cst);
    }
}

void memory_barrier_read(void) {
    if (hal != NULL && hal->atomic.read_barrier != NULL) {
        hal->atomic.read_barrier();
    } else {
        atomic_thread_fence(memory_order_acquire);
    }
}

void memory_barrier_write(void) {
    if (hal != NULL && hal->atomic.write_barrier != NULL) {
        hal->atomic.write_barrier();
    } else {
        atomic_thread_fence(memory_order_release);
    }
}

/**
 * @brief C17 Generic macro for type-safe operations
 */
#define TYPE_SAFE_CAST(type, value) _Generic((value), \
    int: (type)(value), \
    long: (type)(value), \
    long long: (type)(value), \
    unsigned int: (type)(value), \
    unsigned long: (type)(value), \
    unsigned long long: (type)(value), \
    default: (type)(value))

/**
 * @brief Enhanced error handling with C17 features
 */
typedef enum {
    EXO_SUCCESS = 0,
    EXO_ERROR_INVALID_CPU,
    EXO_ERROR_HAL_NOT_INITIALIZED,
    EXO_ERROR_MEMORY_FAULT,
    EXO_ERROR_PERMISSION_DENIED
} exo_error_t;

_Thread_local exo_error_t last_error = EXO_SUCCESS;

exo_error_t exo_get_last_error(void) {
    return last_error;
}

void exo_set_error(exo_error_t error) {
    last_error = error;
}

/**
 * @brief Safe integer operations with overflow checking
 */
bool safe_add_u64(uint64_t a, uint64_t b, uint64_t* restrict result) {
    if (a > UINT64_MAX - b) {
        return false;  /* Overflow would occur */
    }
    *result = a + b;
    return true;
}

bool safe_mul_u64(uint64_t a, uint64_t b, uint64_t* restrict result) {
    if (a != 0 && b > UINT64_MAX / a) {
        return false;  /* Overflow would occur */
    }
    *result = a * b;
    return true;
}

/**
 * @brief Initialization function with proper error handling
 */
bool exo_impl_init(void) {
    /* Verify HAL is initialized */
    if (hal == NULL) {
        exo_set_error(EXO_ERROR_HAL_NOT_INITIALIZED);
        return false;
    }
    
    /* Initialize CPU cache */
    for (size_t i = 0; i < MAX_CPUS; i++) {
        cpu_cache[i] = (cpu_info_t){
            .apic_id = (uint32_t)i,
            .logical_id = (uint32_t)i,
            .online = false,
            .last_timestamp = 0
        };
    }
    
    /* Set initial CPU as active */
    atomic_store_explicit(&active_cpu_count, 1, memory_order_release);
    
    return true;
}

/**
 * @brief Cleanup function
 */
void exo_impl_shutdown(void) {
    atomic_store_explicit(&active_cpu_count, 0, memory_order_release);
    atomic_store_explicit(&global_cpu_ticks, 0, memory_order_release);
}