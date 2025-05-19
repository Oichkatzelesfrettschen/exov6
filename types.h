#pragma once

typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;
typedef unsigned long long uint64;
typedef unsigned long uintptr_t;
typedef unsigned int size_t;

#ifdef __x86_64__
typedef unsigned long long pde_t;
#else
typedef unsigned int pde_t;
#endif
