#pragma once

/**
 * @file hal/memory.h
 * @brief Hardware Abstraction Layer for memory management
 * 
 * Pure C17 implementation for platform-agnostic memory operations.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

// Page size (4KB for both x86_64 and AArch64)
#define HAL_PAGE_SIZE 4096U
#define HAL_PAGE_SHIFT 12U
#define HAL_PAGE_MASK (~(HAL_PAGE_SIZE - 1))

// Page table entry flags (common subset)
typedef enum {
    HAL_PTE_PRESENT  = (1U << 0),  // Page is present
    HAL_PTE_WRITE    = (1U << 1),  // Page is writable
    HAL_PTE_USER     = (1U << 2),  // User accessible
    HAL_PTE_NOCACHE  = (1U << 3),  // Disable caching
    HAL_PTE_ACCESSED = (1U << 4),  // Page was accessed
    HAL_PTE_DIRTY    = (1U << 5),  // Page was written
    HAL_PTE_HUGE     = (1U << 6),  // Huge page (2MB/1GB)
    HAL_PTE_GLOBAL   = (1U << 7),  // Global page
    HAL_PTE_EXECUTE  = (1U << 8),  // Executable (NX bit inverted)
} hal_pte_flags_t;

// Physical and virtual address types
typedef uint64_t hal_paddr_t;  // Physical address
typedef uint64_t hal_vaddr_t;  // Virtual address
typedef uint64_t hal_pte_t;    // Page table entry

// Page table structure (opaque, arch-specific)
typedef struct hal_pagetable hal_pagetable_t;

/**
 * @brief Initialize memory subsystem
 * @return 0 on success, negative on error
 */
int32_t hal_memory_init(void);

/**
 * @brief Create new page table
 * @return Pointer to page table or NULL on error
 */
hal_pagetable_t* hal_pagetable_create(void);

/**
 * @brief Destroy page table
 * @param pt Page table to destroy
 */
void hal_pagetable_destroy(hal_pagetable_t* pt);

/**
 * @brief Map virtual to physical address
 * @param pt Page table
 * @param vaddr Virtual address
 * @param paddr Physical address
 * @param size Size to map (must be page-aligned)
 * @param flags Mapping flags
 * @return 0 on success, negative on error
 */
int32_t hal_page_map(hal_pagetable_t* pt, hal_vaddr_t vaddr, 
                     hal_paddr_t paddr, size_t size, uint32_t flags);

/**
 * @brief Unmap virtual address range
 * @param pt Page table
 * @param vaddr Virtual address
 * @param size Size to unmap
 * @return 0 on success, negative on error
 */
int32_t hal_page_unmap(hal_pagetable_t* pt, hal_vaddr_t vaddr, size_t size);

/**
 * @brief Get physical address for virtual address
 * @param pt Page table
 * @param vaddr Virtual address
 * @return Physical address or 0 if not mapped
 */
hal_paddr_t hal_page_translate(hal_pagetable_t* pt, hal_vaddr_t vaddr);

/**
 * @brief Switch to page table
 * @param pt Page table to activate
 */
void hal_pagetable_switch(hal_pagetable_t* pt);

/**
 * @brief Get current page table
 * @return Current active page table
 */
hal_pagetable_t* hal_pagetable_current(void);

/**
 * @brief Convert physical to virtual address (kernel direct map)
 * @param paddr Physical address
 * @return Virtual address
 */
static inline hal_vaddr_t hal_p2v(hal_paddr_t paddr) {
    // Assumes kernel direct mapping at high addresses
    extern hal_vaddr_t hal_kernel_base;
    return paddr + hal_kernel_base;
}

/**
 * @brief Convert virtual to physical address (kernel direct map)
 * @param vaddr Virtual address
 * @return Physical address
 */
static inline hal_paddr_t hal_v2p(hal_vaddr_t vaddr) {
    extern hal_vaddr_t hal_kernel_base;
    return vaddr - hal_kernel_base;
}

/**
 * @brief Round up to page boundary
 * @param addr Address to round
 * @return Page-aligned address
 */
static inline uintptr_t hal_page_round_up(uintptr_t addr) {
    return (addr + HAL_PAGE_SIZE - 1) & HAL_PAGE_MASK;
}

/**
 * @brief Round down to page boundary
 * @param addr Address to round
 * @return Page-aligned address
 */
static inline uintptr_t hal_page_round_down(uintptr_t addr) {
    return addr & HAL_PAGE_MASK;
}

// Compile-time assertions
_Static_assert(HAL_PAGE_SIZE == (1U << HAL_PAGE_SHIFT), "Page size mismatch");
_Static_assert((HAL_PAGE_SIZE & (HAL_PAGE_SIZE - 1)) == 0, "Page size not power of 2");