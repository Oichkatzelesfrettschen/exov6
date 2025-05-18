typedef unsigned int   uint;
typedef unsigned short ushort;
typedef unsigned char  uchar;
typedef unsigned long long uint64;

#ifdef __x86_64__
typedef uint64 pde_t;
#else
typedef uint pde_t;
#endif
