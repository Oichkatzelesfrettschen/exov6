#pragma once

/**
 * Minimal stdint definitions for freestanding builds.
 * When compiling with \c -nostdinc the system <stdint.h> may not be
 * available, so we provide the required typedefs here unconditionally.
 */

#ifndef _STDINT_H
#define _STDINT_H

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

#endif /* _STDINT_H */
