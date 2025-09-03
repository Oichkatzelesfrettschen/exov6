/* stdint.h - Integer types for ExoKernel */
#ifndef _STDINT_H
#define _STDINT_H
typedef signed char int8_t;
typedef short int16_t;
typedef int int32_t;
typedef long long int64_t;
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;
#ifdef __x86_64__
typedef unsigned long size_t;
typedef unsigned long uintptr_t;
typedef long intptr_t;
#else
// size_t defined by compiler - avoid redefinition
#ifndef __SIZE_TYPE__
typedef unsigned int size_t;
#endif
typedef unsigned int uintptr_t;
typedef int intptr_t;
#endif
#endif
