#pragma once

/* Use system stdint.h when available, fallback to our custom one */
#if defined(__STDC_HOSTED__) && __STDC_HOSTED__ == 1
  #include <stdint.h>
  #include <stddef.h>
#else
  #include "stdint.h"
  #include <stddef.h>
#endif

typedef uint8_t  uchar;
typedef uint16_t ushort;
typedef uint32_t uint;
typedef uint32_t uint32;
typedef uint64_t uint64;
typedef uintptr_t uintptr;
