#pragma once

#include <stdint.h>

// Basic integral types used throughout xv6
typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;
// typedef unsigned long long uint64; // Commented out to resolve conflict with kernel/types.h's uint64 via uint64_t
typedef signed long long int64; // This might also need adjustment later if conflicts arise

// Sized integer aliases (fallbacks for our small libc)
// These are commented out to prefer system's stdint.h
// typedef unsigned int uint32_t;
// typedef int int32_t;
// typedef unsigned long long uint64_t;
// typedef long long int64_t;
// typedef unsigned short uint16_t;
// typedef short int16_t;
// typedef unsigned char uint8_t;
// typedef signed char int8_t;

// Pointer-sized and size types
typedef unsigned long uintptr_t; // This might also conflict if system provides it
// typedef unsigned int size_t; // Commented out to prefer system's stddef.h

#ifdef __x86_64__
typedef unsigned long long pde_t;
#else
typedef unsigned int pde_t;
#endif
