#pragma once

#include <stdint.h>

// Basic integral types used throughout xv6
typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;
typedef uint64_t uint64;
typedef signed long long int64;

/**
 * @brief Sized integer aliases for environments lacking <stdint.h>.
 *
 * When the standard types are already provided, these definitions are
 * omitted to avoid conflicts during userland compilation.
 */
#ifndef UINT32_MAX
typedef unsigned int uint32_t;
typedef int int32_t;
typedef unsigned long long uint64_t;
typedef long long int64_t;
typedef unsigned short uint16_t;
typedef short int16_t;
typedef unsigned char uint8_t;
typedef signed char int8_t;
#endif

// Pointer-sized and size types
#ifndef UINTPTR_MAX
typedef unsigned long uintptr_t;
#endif
// Use compiler-provided definition for size_t when available
#ifndef __SIZE_TYPE__
typedef unsigned long size_t;
#else
typedef __SIZE_TYPE__ size_t;
#endif

#ifdef __x86_64__
typedef unsigned long long pde_t;
#else
typedef unsigned int pde_t;
#endif
