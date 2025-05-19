#pragma once


#include <stdint.h>

typedef uint8_t  uchar;
typedef uint16_t ushort;
typedef uint32_t uint;
typedef uint64_t uint64;

#ifdef __x86_64__
typedef uint64_t pde_t;
typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;
typedef unsigned long long uint64;

typedef unsigned long uintptr_t;
typedef unsigned long size_t;
#else

typedef uint32_t pde_t;
typedef uint32_t uintptr_t;
typedef uint32_t size_t;

#endif
