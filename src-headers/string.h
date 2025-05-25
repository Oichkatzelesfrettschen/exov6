#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include <stddef.h>
void *memmove(void *dst, const void *src, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
#ifdef __cplusplus
}
#endif
