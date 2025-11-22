#pragma once
#include <stddef.h>
void *memmove(void *dst, const void *src, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
void *memcpy(void *dst, const void *src, size_t n);
void *memset(void *dst, int c, size_t n);
size_t strlen(const char *s);
int strcmp(const char *s1, const char *s2);
int strncmp(const char *s1, const char *s2, size_t n);
char *strncpy(char *dst, const char *src, size_t n);
char *strcpy(char *dst, const char *src);
char *strrchr(const char *s, int c);
char *strchr(const char *s, int c);
char *strcat(char *dst, const char *src);
