#pragma once

/**
 * Minimal stdint definitions for freestanding builds.
 * When compiling with \c -nostdinc the system <stdint.h> may not be
 * available, so we provide the required typedefs here unconditionally.
 * However, when system headers are available, defer to them.
 */

#ifndef PHOENIX_STDINT_H
#define PHOENIX_STDINT_H

/* Try to use system stdint.h first if available */
#if defined(__has_include)
  #if __has_include(<stdint.h>)
    #include_next <stdint.h>
    #define PHOENIX_SYSTEM_STDINT_USED 1
  #endif
#endif

/* Only define our types if system stdint.h is not available */
#ifndef PHOENIX_SYSTEM_STDINT_USED

/* Avoid conflicts with system stdint.h */
#ifndef _STDINT_H
#define _STDINT_H
#endif

#ifndef __int8_t_defined
#define __int8_t_defined
typedef signed char int8_t;
typedef short int16_t;
typedef int int32_t;
typedef long long int64_t;
#endif

#ifndef __uint8_t_defined
#define __uint8_t_defined
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;
#endif

#ifndef __intptr_t_defined
#define __intptr_t_defined
typedef long intptr_t;
typedef unsigned long uintptr_t;
#endif

/* Least-width integer types required by stdatomic.h */
#ifndef __int_least8_t_defined
#define __int_least8_t_defined
typedef int8_t int_least8_t;
typedef uint8_t uint_least8_t;
typedef int16_t int_least16_t;
typedef uint16_t uint_least16_t;
typedef int32_t int_least32_t;
typedef uint32_t uint_least32_t;
typedef int64_t int_least64_t;
typedef uint64_t uint_least64_t;
#endif

/* Fast minimum-width integer types */
#ifndef __int_fast8_t_defined
#define __int_fast8_t_defined
typedef int8_t int_fast8_t;
typedef uint8_t uint_fast8_t;
typedef int16_t int_fast16_t;
typedef uint16_t uint_fast16_t;
typedef int32_t int_fast32_t;
typedef uint32_t uint_fast32_t;
typedef int64_t int_fast64_t;
typedef uint64_t uint_fast64_t;
#endif

/* Maximum-width integer types */
#ifndef __intmax_t_defined
#define __intmax_t_defined
typedef int64_t intmax_t;
typedef uint64_t uintmax_t;
#endif

#endif /* !PHOENIX_SYSTEM_STDINT_USED */

#endif /* PHOENIX_STDINT_H */
