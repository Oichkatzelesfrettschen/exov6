#pragma once

typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char  uchar;
typedef unsigned long long uint64;
typedef uint pde_t;

typedef unsigned char uchar;
typedef unsigned long long uint64;

typedef unsigned long uintptr_t;

#ifdef __x86_64__i
typedef unsigned long long pde_t;
#else
typedef unsigned int pde_t;
#endif
