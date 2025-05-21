#pragma once

#include <stdint.h>

typedef uint8_t  uchar;
typedef uint16_t ushort;
typedef uint32_t uint;
typedef uint64_t uint64;
typedef signed long long int64;
typedef unsigned int size_t;

#ifdef __x86_64__
typedef unsigned long long pde_t;
typedef unsigned long uintptr_t;
#else
typedef uint32_t pde_t;
typedef uint32_t uintptr_t;
#endif

