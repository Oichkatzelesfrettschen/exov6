#pragma once

/**
 * @file stdlib.h
 * @brief Unified standard library for FeuerBird ExoKernel
 * 
 * C17-compliant implementation harmonizing kernel, libos, and userland zones.
 * This synthesizes POSIX-2024 requirements with exokernel architecture.
 */

#include <stddef.h>
#include <stdint.h>

// Environment and process control
_Noreturn void exit(int status);
_Noreturn void _Exit(int status);
_Noreturn void abort(void);
int atexit(void (*func)(void));
int at_quick_exit(void (*func)(void));
_Noreturn void quick_exit(int status);

// Memory management - unified across zones
void* malloc(size_t size);
void* calloc(size_t nmemb, size_t size);
void* realloc(void* ptr, size_t size);
void* aligned_alloc(size_t alignment, size_t size);
void free(void* ptr);

// String conversion - harmonized implementations
int atoi(const char* nptr);
long atol(const char* nptr);
long long atoll(const char* nptr);
double atof(const char* nptr);
double strtod(const char* restrict nptr, char** restrict endptr);
float strtof(const char* restrict nptr, char** restrict endptr);
long double strtold(const char* restrict nptr, char** restrict endptr);
long strtol(const char* restrict nptr, char** restrict endptr, int base);
long long strtoll(const char* restrict nptr, char** restrict endptr, int base);
unsigned long strtoul(const char* restrict nptr, char** restrict endptr, int base);
unsigned long long strtoull(const char* restrict nptr, char** restrict endptr, int base);

// Random number generation - cryptographically aware
int rand(void);
void srand(unsigned int seed);
int rand_r(unsigned int* seedp);

// Sorting and searching - optimized for cache locality
void* bsearch(const void* key, const void* base, size_t nmemb, size_t size,
              int (*compar)(const void*, const void*));
void qsort(void* base, size_t nmemb, size_t size,
           int (*compar)(const void*, const void*));

// Integer arithmetic
int abs(int j);
long labs(long j);
long long llabs(long long j);
typedef struct { int quot; int rem; } div_t;
typedef struct { long quot; long rem; } ldiv_t;
typedef struct { long long quot; long long rem; } lldiv_t;
div_t div(int numer, int denom);
ldiv_t ldiv(long numer, long denom);
lldiv_t lldiv(long long numer, long long denom);

// Multibyte/wide character conversion
int mblen(const char* s, size_t n);
int mbtowc(wchar_t* restrict pwc, const char* restrict s, size_t n);
int wctomb(char* s, wchar_t wc);
size_t mbstowcs(wchar_t* restrict pwcs, const char* restrict s, size_t n);
size_t wcstombs(char* restrict s, const wchar_t* restrict pwcs, size_t n);

// Environment access
char* getenv(const char* name);
int setenv(const char* name, const char* value, int overwrite);
int unsetenv(const char* name);
int putenv(char* string);

// System commands
int system(const char* command);

// Path manipulation  
char* realpath(const char* restrict path, char* restrict resolved_path);

// Pseudo-random
#define RAND_MAX 2147483647

// Exit codes
#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1

// MB_CUR_MAX - maximum bytes in multibyte character
#define MB_CUR_MAX 4

// Null pointer constant
#ifndef NULL
#define NULL ((void*)0)
#endif

// Static assertions for ABI compatibility
_Static_assert(sizeof(div_t) == 2 * sizeof(int), "div_t must be two ints");
_Static_assert(sizeof(ldiv_t) == 2 * sizeof(long), "ldiv_t must be two longs");
_Static_assert(RAND_MAX >= 32767, "RAND_MAX must be at least 32767");

// Exokernel-specific memory extensions (harmonized with standard interface)
#ifdef EXO_EXTENSIONS
void* exo_malloc_cap(size_t size, uint32_t rights);
void exo_free_cap(void* ptr);
size_t exo_malloc_usable_size(const void* ptr);
#endif