#pragma once

/**
 * @file memlayout.h
 * @brief Consolidated memory layout and page constants for FeuerBird
 * 
 * Central location for all memory-related constants to avoid conflicts.
 * Pure C17 implementation with architecture-specific sections.
 */

#ifndef __ASSEMBLER__
#include <stdint.h>
#endif

// ============================================================================
// PAGE SIZE CONSTANTS - SINGLE DEFINITION POINT
// ============================================================================

#ifndef PGSIZE
#define PGSIZE     4096           // Standard page size (4KB)
#define PGSHIFT    12             // Page size as shift (2^12 = 4096)
#define PGMASK     (PGSIZE - 1)   // Page offset mask
#endif

// Page alignment macros
#define PGROUNDUP(sz)   (((sz) + PGSIZE - 1) & ~(PGSIZE - 1))
#define PGROUNDDOWN(a)  ((a) & ~(PGSIZE - 1))

// ============================================================================
// MEMORY LAYOUT
// ============================================================================

#define EXTMEM 0x100000 // Start of extended memory

// 32-bit memory layout parameters (default)
#define PHYSTOP_32 0xE000000            // Top physical memory
#define DEVSPACE_32 0xFE000000          // Other devices are at high addresses
#define KERNBASE_32 0x80000000          // First kernel virtual address
#define KERNLINK_32 (KERNBASE_32 + EXTMEM) // Address where kernel is linked

// 64-bit memory layout parameters
#define KERNBASE_64 0xffffffff80000000ULL
#define KERNLINK_64 (KERNBASE_64 + EXTMEM)
#define PHYSTOP_64 0xE000000
#define DEVSPACE_64 0xfffffffffe000000ULL

// Select layout depending on compilation mode
#ifdef __x86_64__
#define KERNBASE KERNBASE_64
#define KERNLINK KERNLINK_64
#define PHYSTOP PHYSTOP_64
#define DEVSPACE DEVSPACE_64
#define KERNSIZE (PHYSTOP_64 - EXTMEM)  // Kernel size
#else
#define KERNBASE KERNBASE_32
#define KERNLINK KERNLINK_32
#define PHYSTOP PHYSTOP_32
#define DEVSPACE DEVSPACE_32
#define KERNSIZE (PHYSTOP_32 - EXTMEM)  // Kernel size
#endif

// Virtual to Physical and Physical to Virtual conversions
#ifdef __x86_64__
#define V2P(a) (((uint64_t)(a)) - KERNBASE)
#define P2V(a) ((void *)((uint64_t)(a) + KERNBASE))
#else
#define V2P(a) (((uint32_t)(a)) - KERNBASE)
#define P2V(a) ((void *)(((char *)(a)) + KERNBASE))
#endif

#define V2P_WO(x) ((x) - KERNBASE) // same as V2P, but without casts
#define P2V_WO(x) ((x) + KERNBASE) // same as P2V, but without casts
