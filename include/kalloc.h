#pragma once

/**
 * @file kalloc.h
 * @brief Kernel memory allocator interface
 * 
 * Pure C17 kernel memory allocation interface with capability integration.
 * Provides page-aligned allocation for kernel data structures and buffers.
 */

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Allocate a page of kernel memory (4096 bytes)
 * @return Pointer to allocated page, or NULL on failure
 * 
 * The returned memory is:
 * - Page-aligned (4096-byte boundary)
 * - Zero-initialized
 * - Suitable for kernel data structures
 * - Must be freed with kfree()
 */
char *kalloc(void);

/**
 * @brief Free a page of kernel memory
 * @param ptr Pointer returned by kalloc(), must be page-aligned
 * 
 * The memory must have been allocated by kalloc().
 * Passing NULL is safe and ignored.
 * Passing non-page-aligned pointers causes undefined behavior.
 */
void kfree(char *ptr);

/**
 * @brief Initialize kernel memory allocator
 * 
 * Called during kernel boot to set up the page allocator.
 * Must be called before any kalloc() calls.
 */
void kinit1(void *vstart, void *vend);
void kinit2(void *vstart, void *vend);

#ifdef __cplusplus
}
#endif