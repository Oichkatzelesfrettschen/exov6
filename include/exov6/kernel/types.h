#pragma once

/* Ensure this is only used in kernel */
#if !defined(__KERNEL__) && !defined(EXO_KERNEL)
#error "Kernel headers (include/exov6/kernel/*.h) should not be included in userspace! Use <sys/types.h> or standard headers."
#endif

/* Use system stdint.h when available, fallback to our custom one */
#if defined(__STDC_HOSTED__) && __STDC_HOSTED__ == 1
  #include <stdint.h>
  #include <stddef.h>
#else
  /* In kernel mode, rely on the moved POSIX headers */
  #include <exov6/posix/stdint.h>
  #include <exov6/posix/stddef.h>
#endif

#include "compiler_attrs.h"

/* Legacy/Convenience types */
typedef uint8_t  uchar;
typedef uint16_t ushort;
typedef uint32_t uint;
typedef uint32_t uint32;
typedef uint64_t uint64;
typedef uintptr_t uintptr;

/* Type Hygiene: Strongly separated address types */
typedef uintptr_t kernel_ptr; /* Virtual address in kernel space */
typedef uintptr_t user_ptr;   /* Virtual address in user space */
typedef uintptr_t phys_addr;  /* Physical address */

/* Ensure 64-bit types are used where appropriate */
_Static_assert(sizeof(uintptr) == 8, "Kernel requires 64-bit pointers");
_Static_assert(sizeof(uint64) == 8, "uint64 must be 64-bit");
