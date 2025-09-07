#pragma once

/**
 * @file hal/cpu.h
 * @brief Hardware Abstraction Layer for CPU operations
 * 
 * Pure C17 implementation providing platform-agnostic CPU operations.
 * Architecture-specific implementations in src/arch/{x86_64,aarch64}/
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

// Forward declarations
struct hal_context;
struct hal_trapframe;

/**
 * @brief CPU context for context switching
 * Architecture-specific, defined in arch headers
 */
typedef struct hal_context hal_context_t;

/**
 * @brief Trap frame for interrupt/exception handling
 * Architecture-specific, defined in arch headers
 */
typedef struct hal_trapframe hal_trapframe_t;

/**
 * @brief CPU identification
 */
typedef struct {
    uint32_t id;           // Logical CPU ID
    uint32_t arch_id;      // Architecture-specific ID (APIC ID, MPIDR, etc.)
    bool is_bsp;           // Is bootstrap processor
    bool online;           // Is CPU online
} hal_cpu_info_t;

/**
 * @brief Initialize CPU subsystem
 * @return 0 on success, negative on error
 */
int32_t hal_cpu_init(void);

/**
 * @brief Get current CPU information
 * @return Pointer to current CPU info
 */
const hal_cpu_info_t* hal_cpu_current(void);

/**
 * @brief Get CPU ID
 * @return Current CPU ID
 */
uint32_t hal_cpu_id(void);

/**
 * @brief Context switch between threads
 * @param old Pointer to save current context
 * @param new Context to switch to
 */
void hal_context_switch(hal_context_t** old, hal_context_t* new);

/**
 * @brief Enable interrupts
 */
void hal_interrupts_enable(void);

/**
 * @brief Disable interrupts
 */
void hal_interrupts_disable(void);

/**
 * @brief Save interrupt state and disable
 * @return Previous interrupt state
 */
uint64_t hal_interrupts_save_disable(void);

/**
 * @brief Restore interrupt state
 * @param state Previous state from hal_interrupts_save_disable
 */
void hal_interrupts_restore(uint64_t state);

/**
 * @brief Check if interrupts are enabled
 * @return true if enabled, false otherwise
 */
bool hal_interrupts_enabled(void);

/**
 * @brief Halt CPU until interrupt
 */
void hal_cpu_halt(void);

/**
 * @brief Pause CPU briefly (for spinlock backoff)
 */
void hal_cpu_pause(void);

/**
 * @brief Memory barrier - full fence
 */
void hal_memory_barrier(void);

/**
 * @brief Read barrier
 */
void hal_read_barrier(void);

/**
 * @brief Write barrier
 */
void hal_write_barrier(void);

/**
 * @brief Invalidate TLB entry
 * @param addr Virtual address to invalidate
 */
void hal_tlb_invalidate(void* addr);

/**
 * @brief Flush entire TLB
 */
void hal_tlb_flush_all(void);

/**
 * @brief Read timestamp counter
 * @return Current timestamp value
 */
uint64_t hal_read_timestamp(void);

// Compile-time assertions for C17 compliance
_Static_assert(sizeof(uint32_t) == 4, "uint32_t must be 4 bytes");
_Static_assert(sizeof(uint64_t) == 8, "uint64_t must be 8 bytes");