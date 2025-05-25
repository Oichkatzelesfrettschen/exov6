#pragma once
#include "types.h"
#include "../exo.h"

/*
 * Exokernel CPU interface used by user-level schedulers.
 *
 * exo_swtch(old, new) wraps the low-level swtch() primitive.  Both
 * arguments must point to a context_t structure describing the saved
 * callee-saved registers and stack pointer.  The caller must preserve
 * caller-saved registers according to the System V ABI.  On return,
 * execution resumes on the context pointed to by *old.
 */

#ifndef EXO_CONTEXT_T
#define EXO_CONTEXT_T
#if defined(__x86_64__)
struct context64 {
  uint64_t r15;
  uint64_t r14;
  uint64_t r13;
  uint64_t r12;
  uint64_t rbx;
  uint64_t rbp;
  uint64_t rip;
};
typedef struct context64 context_t;
#elif defined(__aarch64__)
struct context64 {
  uint64_t x19;
  uint64_t x20;
  uint64_t x21;
  uint64_t x22;
  uint64_t x23;
  uint64_t x24;
  uint64_t x25;
  uint64_t x26;
  uint64_t x27;
  uint64_t x28;
  uint64_t fp;
  uint64_t lr;
};
typedef struct context64 context_t;
#else
struct context {
  uint32_t edi;
  uint32_t esi;
  uint32_t ebx;
  uint32_t ebp;
  uint32_t eip;
};
typedef struct context context_t;
#endif
#endif /* EXO_CONTEXT_T */

void swtch(context_t **old, context_t *new);
static inline void cap_yield(context_t **old, context_t *target) {
  swtch(old, target);
}

[[nodiscard]] int exo_yield_to(exo_cap target);
