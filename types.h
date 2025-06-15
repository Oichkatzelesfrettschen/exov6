#pragma once

#include <stdint.h>

// Basic integral types used throughout xv6
typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;
typedef unsigned long long uint64;
typedef signed long long int64;

// Sized integer aliases (fallbacks for our small libc)
typedef unsigned int uint32_t;
typedef int int32_t;
typedef unsigned long long uint64_t;
typedef long long int64_t;
typedef unsigned short uint16_t;
typedef short int16_t;
typedef unsigned char uint8_t;
typedef signed char int8_t;

// Pointer-sized and size types
typedef unsigned long uintptr_t;
// Use compiler-provided definition to avoid mismatched size_t with system headers
typedef __SIZE_TYPE__ size_t;

#ifdef __x86_64__
typedef unsigned long long pde_t;
#else
typedef unsigned int pde_t;
#endif
