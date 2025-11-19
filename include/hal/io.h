#pragma once

/**
 * @file hal/io.h
 * @brief Hardware Abstraction Layer for I/O operations
 * 
 * Pure C17 implementation for platform-agnostic I/O.
 * Handles both port I/O (x86) and memory-mapped I/O (ARM).
 */

#include <stdint.h>
#include <stddef.h>

/**
 * @brief I/O port type (x86) or MMIO address (ARM)
 */
typedef uint64_t hal_io_addr_t;

/**
 * @brief Read 8-bit value from I/O port/MMIO
 * @param addr Port number or MMIO address
 * @return Value read
 */
uint8_t hal_io_read8(hal_io_addr_t addr);

/**
 * @brief Write 8-bit value to I/O port/MMIO
 * @param addr Port number or MMIO address
 * @param value Value to write
 */
void hal_io_write8(hal_io_addr_t addr, uint8_t value);

/**
 * @brief Read 16-bit value from I/O port/MMIO
 * @param addr Port number or MMIO address
 * @return Value read
 */
uint16_t hal_io_read16(hal_io_addr_t addr);

/**
 * @brief Write 16-bit value to I/O port/MMIO
 * @param addr Port number or MMIO address
 * @param value Value to write
 */
void hal_io_write16(hal_io_addr_t addr, uint16_t value);

/**
 * @brief Read 32-bit value from I/O port/MMIO
 * @param addr Port number or MMIO address
 * @return Value read
 */
uint32_t hal_io_read32(hal_io_addr_t addr);

/**
 * @brief Write 32-bit value to I/O port/MMIO
 * @param addr Port number or MMIO address
 * @param value Value to write
 */
void hal_io_write32(hal_io_addr_t addr, uint32_t value);

/**
 * @brief Read 64-bit value from MMIO
 * @param addr MMIO address
 * @return Value read
 */
uint64_t hal_io_read64(hal_io_addr_t addr);

/**
 * @brief Write 64-bit value to MMIO
 * @param addr MMIO address
 * @param value Value to write
 */
void hal_io_write64(hal_io_addr_t addr, uint64_t value);

/**
 * @brief Read multiple 32-bit values from I/O port/MMIO
 * @param addr Port number or MMIO address
 * @param buffer Destination buffer
 * @param count Number of 32-bit values to read
 */
void hal_io_read32_rep(hal_io_addr_t addr, uint32_t* buffer, size_t count);

/**
 * @brief Write multiple 32-bit values to I/O port/MMIO
 * @param addr Port number or MMIO address
 * @param buffer Source buffer
 * @param count Number of 32-bit values to write
 */
void hal_io_write32_rep(hal_io_addr_t addr, const uint32_t* buffer, size_t count);

/**
 * @brief I/O memory barrier
 * Ensures all I/O operations complete before continuing
 */
void hal_io_barrier(void);

/**
 * @brief Map MMIO region (for architectures that need it)
 * @param phys_addr Physical address
 * @param size Size of region
 * @return Virtual address or 0 on error
 */
hal_io_addr_t hal_io_map(uint64_t phys_addr, size_t size);

/**
 * @brief Unmap MMIO region
 * @param virt_addr Virtual address from hal_io_map
 * @param size Size of region
 */
void hal_io_unmap(hal_io_addr_t virt_addr, size_t size);

// Platform-specific I/O delay (for legacy devices)
static inline void hal_io_delay(void) {
    // Small delay for I/O timing
    for (volatile int32_t i = 0; i < 100; i++) {
        __asm__ volatile("" ::: "memory");
    }
}

// Compile-time assertions
_Static_assert(sizeof(hal_io_addr_t) >= sizeof(void*), 
               "I/O address type must hold pointers");
