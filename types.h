#pragma once

#include "stdint.h"

/*
 * Basic sized aliases used throughout the kernel and user-space
 * code.  These mirror the standard int{8,16,32,64}_t types but
 * have shorter names that match the historic xv6 code style.
 */
typedef int8_t   int8;
typedef uint8_t  uint8;
typedef int16_t  int16;
typedef uint16_t uint16;
typedef int32_t  int32;
typedef uint32_t uint32;
typedef int64_t  int64;
typedef uint64_t uint64;

/* Common unsigned aliases used across the code base */
typedef uint8  uchar;
typedef uint16 ushort;
typedef uint32 uint;

/*
 * Pointer-sized types and page table entry types depend on the
 * target architecture width.  Both x86_64 and aarch64 are treated
 * as 64-bit platforms; everything else defaults to 32-bit.
 */
#if defined(__x86_64__) || defined(__aarch64__)
typedef unsigned long uintptr_t;
typedef long          intptr_t;
typedef unsigned long size_t;
typedef uint64        pde_t;
typedef uint64        pte_t;
typedef uint64        pdpe_t;
typedef uint64        pml4e_t;
#else
typedef uint32        uintptr_t;
typedef int32         intptr_t;
typedef uint32        size_t;
typedef uint32        pde_t;
typedef uint32        pte_t;
#endif

