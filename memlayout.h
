#pragma once

// Memory layout

#define EXTMEM 0x100000 // Start of extended memory

// 32-bit memory layout parameters
#define PHYSTOP 0xE000000            // Top physical memory
#define DEVSPACE 0xFE000000          // Other devices are at high addresses
#define KERNBASE 0x80000000          // First kernel virtual address
#define KERNLINK (KERNBASE + EXTMEM) // Address where kernel is linked

// 64-bit memory layout parameters
#define KERNBASE64 0xffffffff80000000ULL
#define KERNLINK64 (KERNBASE64 + EXTMEM)
#define PHYSTOP64 0xE000000
#define DEVSPACE64 0xfffffffffe000000ULL

// Select layout depending on compilation mode
#ifdef __x86_64__
#undef KERNBASE
#undef KERNLINK
#undef PHYSTOP
#undef DEVSPACE
#define KERNBASE KERNBASE64
#define KERNLINK KERNLINK64
#define PHYSTOP PHYSTOP64
#define DEVSPACE DEVSPACE64
#endif

#ifdef __x86_64__
#define V2P(a) (((uint64)(a)) - KERNBASE)
#define P2V(a) ((void *)((uint64)(a) + KERNBASE))
#else
#define V2P(a) (((uint)(a)) - KERNBASE)
#define P2V(a) ((void *)(((char *)(a)) + KERNBASE))
#endif

#define V2P_WO(x) ((x) - KERNBASE) // same as V2P, but without casts
#define P2V_WO(x) ((x) + KERNBASE) // same as P2V, but without casts
