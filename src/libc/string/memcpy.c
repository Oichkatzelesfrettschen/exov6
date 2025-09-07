/*
 * memcpy.c - Modern C17 implementation of memcpy
 * 
 * POSIX-2024 compliant memory copy function
 * Uses C17 features: restrict pointers, stdint types, static assertions
 */

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdalign.h>

/* Compile-time assertions for platform assumptions */
_Static_assert(sizeof(void*) == 8, "64-bit platform required");
_Static_assert(alignof(max_align_t) >= 8, "8-byte alignment required");

/**
 * memcpy - Copy memory area
 * @dest: Destination buffer (must not overlap with src)
 * @src: Source buffer (must not overlap with dest)
 * @n: Number of bytes to copy
 *
 * Returns: Pointer to dest
 *
 * C17 Features Used:
 * - restrict pointers for optimization
 * - stdint types for portability
 * - inline functions for performance
 * - _Alignas for cache optimization
 */
void *memcpy(void * restrict dest, const void * restrict src, size_t n)
{
    uint8_t * restrict d = (uint8_t * restrict)dest;
    const uint8_t * restrict s = (const uint8_t * restrict)src;
    
    /* Fast path: copy 64-bit words when aligned */
    if (((uintptr_t)d & 7) == 0 && ((uintptr_t)s & 7) == 0) {
        uint64_t * restrict d64 = (uint64_t * restrict)d;
        const uint64_t * restrict s64 = (const uint64_t * restrict)s;
        
        while (n >= sizeof(uint64_t)) {
            *d64++ = *s64++;
            n -= sizeof(uint64_t);
        }
        
        d = (uint8_t * restrict)d64;
        s = (const uint8_t * restrict)s64;
    }
    
    /* Copy remaining bytes */
    while (n--) {
        *d++ = *s++;
    }
    
    return dest;
}

/**
 * memcpy_aligned - Optimized memcpy for aligned buffers
 * @dest: 64-byte aligned destination
 * @src: 64-byte aligned source
 * @n: Size in bytes (should be multiple of 64 for best performance)
 *
 * C17 Feature: Uses _Alignas for cache-line optimization
 */
void *memcpy_aligned(void * restrict dest, const void * restrict src, size_t n)
{
    _Alignas(64) uint64_t * restrict d64 = (uint64_t * restrict)dest;
    _Alignas(64) const uint64_t * restrict s64 = (const uint64_t * restrict)src;
    
    /* Unroll loop for cache-line sized copies */
    while (n >= 64) {
        d64[0] = s64[0];
        d64[1] = s64[1];
        d64[2] = s64[2];
        d64[3] = s64[3];
        d64[4] = s64[4];
        d64[5] = s64[5];
        d64[6] = s64[6];
        d64[7] = s64[7];
        
        d64 += 8;
        s64 += 8;
        n -= 64;
    }
    
    /* Handle remainder */
    if (n > 0) {
        memcpy(d64, s64, n);
    }
    
    return dest;
}