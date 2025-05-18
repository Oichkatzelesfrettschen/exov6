typedef unsigned int   uint;
typedef unsigned short ushort;
typedef unsigned char  uchar;
typedef unsigned long long uint64;

#ifdef __x86_64__
typedef uint64 pde_t;
#else
typedef uint pde_t;

#endif


#endif


typedef unsigned long uintptr_t;

#ifdef __x86_64__
typedef unsigned long uint64;




