#pragma once

#include <stdint.h>

typedef uint8_t  uchar;
typedef uint16_t ushort;
typedef uint32_t uint;
typedef uint64_t uint64;

#ifdef __x86_64__
typedef uint64_t pde_t;
typedef uint64_t uintptr_t;
typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;
typedef unsigned long long uint64;
typedef signed long long int64;

typedef unsigned int uint32_t;
typedef int int32_t;
typedef unsigned long long uint64_t;
typedef long long int64_t;
typedef unsigned short uint16_t;
typedef short int16_t;
typedef unsigned char uint8_t;
typedef signed char int8_t;

typedef unsigned long uintptr_t;
typedef unsigned int size_t;

#ifdef __x86_64__
typedef unsigned long long pde_t;
#else
typedef uint32_t pde_t;
typedef uint32_t uintptr_t;
#endif
