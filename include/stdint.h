#pragma once

/**
 * Minimal stdint definitions for freestanding builds.
 * When compiling with \c -nostdinc the system <stdint.h> may not be
 * available, so we provide the required typedefs here conditionally.
 * For hosted builds, use the system stdint.h instead.
 */

#ifndef __STDC_HOSTED__
/* Freestanding environment - define our own types */
typedef signed char int8_t;
typedef short int16_t;
typedef int int32_t;
typedef long long int64_t;

typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;

typedef long intptr_t;
typedef unsigned long uintptr_t;
#else
/* Hosted environment - use system stdint.h */
#include_next <stdint.h>
#endif
