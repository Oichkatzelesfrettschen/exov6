#pragma once
#include "types.h"

/*
 * Exokernel CPU interface used by user-level schedulers.
 *
 * exo_swtch(old, new) wraps the low-level swtch() primitive.  Both
 * arguments must point to a context_t structure describing the saved
 * callee-saved registers and stack pointer.  The caller must preserve
 * caller-saved registers according to the System V ABI.  On return,
 * execution resumes on the context pointed to by *old.
 */

#ifdef __x86_64__
struct context64 {
  uint64 r15;
  uint64 r14;
  uint64 r13;
  uint64 r12;
  uint64 rbx;
  uint64 rbp;
  uint64 rip;
};
typedef struct context64 context_t;
#else
struct context {
  uint edi;
  uint esi;
  uint ebx;
  uint ebp;
  uint eip;
};
typedef struct context context_t;
#endif

void swtch(context_t **old, context_t *new);
static inline void cap_yield(context_t **old, context_t *target) {
  swtch(old, target);
}
