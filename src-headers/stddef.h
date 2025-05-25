#ifdef __cplusplus
extern "C" {
#endif
#if __has_include_next(<stddef.h>)
#include_next <stddef.h>
#else
typedef __SIZE_TYPE__ size_t;
typedef __PTRDIFF_TYPE__ ptrdiff_t;
#define NULL ((void *)0)
#endif
#ifdef __cplusplus
}
#endif
