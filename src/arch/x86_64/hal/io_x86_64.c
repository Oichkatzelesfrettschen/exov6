/**
 * @file io_x86_64.c
 * @brief x86_64 implementation of HAL I/O interface
 * 
 * Pure C17 implementation for x86_64 port I/O and MMIO.
 */

#include "hal/io.h"
#include <string.h>

// x86_64 uses port I/O for legacy devices
uint8_t hal_io_read8(hal_io_addr_t addr) {
    uint8_t value;
    if (addr < 0x10000) {
        // Port I/O
        __asm__ volatile("inb %1, %0" : "=a"(value) : "Nd"((uint16_t)addr) : "memory");
    } else {
        // MMIO
        value = *(volatile uint8_t*)addr;
    }
    return value;
}

void hal_io_write8(hal_io_addr_t addr, uint8_t value) {
    if (addr < 0x10000) {
        // Port I/O
        __asm__ volatile("outb %0, %1" : : "a"(value), "Nd"((uint16_t)addr) : "memory");
    } else {
        // MMIO
        *(volatile uint8_t*)addr = value;
    }
}

uint16_t hal_io_read16(hal_io_addr_t addr) {
    uint16_t value;
    if (addr < 0x10000) {
        // Port I/O
        __asm__ volatile("inw %1, %0" : "=a"(value) : "Nd"((uint16_t)addr) : "memory");
    } else {
        // MMIO
        value = *(volatile uint16_t*)addr;
    }
    return value;
}

void hal_io_write16(hal_io_addr_t addr, uint16_t value) {
    if (addr < 0x10000) {
        // Port I/O
        __asm__ volatile("outw %0, %1" : : "a"(value), "Nd"((uint16_t)addr) : "memory");
    } else {
        // MMIO
        *(volatile uint16_t*)addr = value;
    }
}

uint32_t hal_io_read32(hal_io_addr_t addr) {
    uint32_t value;
    if (addr < 0x10000) {
        // Port I/O
        __asm__ volatile("inl %1, %0" : "=a"(value) : "Nd"((uint16_t)addr) : "memory");
    } else {
        // MMIO
        value = *(volatile uint32_t*)addr;
    }
    return value;
}

void hal_io_write32(hal_io_addr_t addr, uint32_t value) {
    if (addr < 0x10000) {
        // Port I/O
        __asm__ volatile("outl %0, %1" : : "a"(value), "Nd"((uint16_t)addr) : "memory");
    } else {
        // MMIO
        *(volatile uint32_t*)addr = value;
    }
}

uint64_t hal_io_read64(hal_io_addr_t addr) {
    // x86_64 doesn't have 64-bit port I/O
    return *(volatile uint64_t*)addr;
}

void hal_io_write64(hal_io_addr_t addr, uint64_t value) {
    // x86_64 doesn't have 64-bit port I/O
    *(volatile uint64_t*)addr = value;
}

void hal_io_read32_rep(hal_io_addr_t addr, uint32_t* buffer, size_t count) {
    if (addr < 0x10000) {
        // Port I/O - use rep insl
        __asm__ volatile(
            "cld\n"
            "rep insl"
            : "+D"(buffer), "+c"(count)
            : "d"((uint16_t)addr)
            : "memory"
        );
    } else {
        // MMIO - read sequentially
        volatile uint32_t* src = (volatile uint32_t*)addr;
        for (size_t i = 0; i < count; i++) {
            buffer[i] = *src;
        }
    }
}

void hal_io_write32_rep(hal_io_addr_t addr, const uint32_t* buffer, size_t count) {
    if (addr < 0x10000) {
        // Port I/O - use rep outsl
        __asm__ volatile(
            "cld\n"
            "rep outsl"
            : "+S"(buffer), "+c"(count)
            : "d"((uint16_t)addr)
            : "memory"
        );
    } else {
        // MMIO - write sequentially
        volatile uint32_t* dst = (volatile uint32_t*)addr;
        for (size_t i = 0; i < count; i++) {
            *dst = buffer[i];
        }
    }
}

void hal_io_barrier(void) {
    // Full memory fence for I/O ordering
    __asm__ volatile("mfence" ::: "memory");
}

hal_io_addr_t hal_io_map(uint64_t phys_addr, size_t size) {
    // In kernel mode with identity mapping, just return the address
    // Real implementation would set up page tables
    UNUSED(size);
    return (hal_io_addr_t)phys_addr;
}

void hal_io_unmap(hal_io_addr_t virt_addr, size_t size) {
    // No-op for identity mapped kernel
    UNUSED(virt_addr);
    UNUSED(size);
}