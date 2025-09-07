#pragma once

/**
 * @file types.h
 * @brief Core type definitions for FeuerBird ExoKernel
 * 
 * Pure C17 implementation with modern type definitions.
 * Legacy typedefs are deprecated and will be removed.
 */

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdnoreturn.h>

// ============================================================================
// DEPRECATED LEGACY TYPES - DO NOT USE IN NEW CODE
// These are maintained ONLY for compatibility during migration
// ============================================================================
#ifdef LEGACY_TYPES_COMPATIBILITY
typedef uint8_t  uchar;    // DEPRECATED: Use uint8_t
typedef uint16_t ushort;   // DEPRECATED: Use uint16_t
typedef uint32_t uint;     // DEPRECATED: Use uint32_t
typedef uint32_t uint32;   // DEPRECATED: Use uint32_t
typedef uint64_t uint64;   // DEPRECATED: Use uint64_t
typedef uintptr_t uintptr; // DEPRECATED: Use uintptr_t

#warning "Legacy types are deprecated. Migrate to stdint.h types."
#endif

// ============================================================================
// MODERN C17 TYPE DEFINITIONS
// ============================================================================

// Page table types (architecture-specific sizes)
#ifdef __x86_64__
typedef uint64_t pde_t;    // Page directory entry
typedef uint64_t pte_t;    // Page table entry
typedef uint64_t pml4e_t;  // Page map level 4 entry
typedef uint64_t pdpe_t;   // Page directory pointer entry
#elif defined(__aarch64__)
typedef uint64_t pde_t;    // Page directory entry
typedef uint64_t pte_t;    // Page table entry
typedef uint64_t pgd_t;    // Page global directory
typedef uint64_t pud_t;    // Page upper directory
typedef uint64_t pmd_t;    // Page middle directory
#else
typedef uint32_t pde_t;    // Page directory entry (32-bit fallback)
typedef uint32_t pte_t;    // Page table entry (32-bit fallback)
#endif

// Physical and virtual address types
typedef uint64_t physaddr_t;  // Physical address
typedef uint64_t virtaddr_t;  // Virtual address

// Size types
typedef size_t    size_t;     // Already from stddef.h
typedef ptrdiff_t offset_t;   // Offset type

// Status/error codes
typedef int32_t status_t;     // Function return status
typedef int32_t error_t;       // Error codes

// Process and thread IDs (pid_t defined in sys/types.h)
typedef int32_t tid_t;         // Thread ID  
typedef uint32_t cpu_id_t;     // CPU ID

/* POSIX file system types are defined in sys/types.h */

// Time types
typedef uint64_t time_ns_t;    // Time in nanoseconds
typedef uint64_t ticks_t;      // System ticks

// Capability types
typedef uint64_t cap_id_t;     // Capability ID
typedef uint32_t cap_rights_t; // Capability rights

// ============================================================================
// COMPILE-TIME ASSERTIONS
// ============================================================================

// Ensure proper sizes
_Static_assert(sizeof(uint8_t) == 1, "uint8_t must be 1 byte");
_Static_assert(sizeof(uint16_t) == 2, "uint16_t must be 2 bytes");
_Static_assert(sizeof(uint32_t) == 4, "uint32_t must be 4 bytes");
_Static_assert(sizeof(uint64_t) == 8, "uint64_t must be 8 bytes");

// Ensure pointer size matches architecture
#ifdef __x86_64__
_Static_assert(sizeof(void*) == 8, "Pointers must be 8 bytes on x86_64");
_Static_assert(sizeof(pte_t) == 8, "PTE must be 8 bytes on x86_64");
#elif defined(__aarch64__)
_Static_assert(sizeof(void*) == 8, "Pointers must be 8 bytes on AArch64");
_Static_assert(sizeof(pte_t) == 8, "PTE must be 8 bytes on AArch64");
#endif

// Ensure alignment of critical types
_Static_assert(_Alignof(uint64_t) >= 8, "uint64_t must be 8-byte aligned");

// ============================================================================
// HELPER MACROS
// ============================================================================

// Min/max that are type-safe
#define MIN(a, b) ({           \
    __typeof__(a) _a = (a);    \
    __typeof__(b) _b = (b);    \
    _a < _b ? _a : _b;         \
})

#define MAX(a, b) ({           \
    __typeof__(a) _a = (a);    \
    __typeof__(b) _b = (b);    \
    _a > _b ? _a : _b;         \
})

// Array size
#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))

// Container of macro
#define container_of(ptr, type, member) ({                 \
    const __typeof__(((type *)0)->member) *__mptr = (ptr); \
    (type *)((char *)__mptr - offsetof(type, member));     \
})

// Alignment macros
#define ALIGN_UP(x, align) (((x) + (align) - 1) & ~((align) - 1))
#define ALIGN_DOWN(x, align) ((x) & ~((align) - 1))
#define IS_ALIGNED(x, align) (((x) & ((align) - 1)) == 0)

// Bit manipulation
#define BIT(n) (1UL << (n))
#define BIT_MASK(n) (BIT(n) - 1)
#define BIT_SET(x, n) ((x) |= BIT(n))
#define BIT_CLEAR(x, n) ((x) &= ~BIT(n))
#define BIT_TEST(x, n) (((x) & BIT(n)) != 0)

// Compiler hints
#define likely(x)   __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

// Memory barriers
#define barrier() __asm__ __volatile__("" ::: "memory")
#define mb()  __sync_synchronize()
#define rmb() barrier()
#define wmb() barrier()

// Unused parameter
#define UNUSED(x) ((void)(x))

// Stringify
#define STRINGIFY(x) #x
#define STRINGIFY_EXPAND(x) STRINGIFY(x)