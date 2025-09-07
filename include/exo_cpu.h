#pragma once
#include "types.h"
#include "exo.h"

/*
 * Exokernel CPU interface used by user-level schedulers.
 *
 * exo_swtch(old, new) wraps the low-level swtch() primitive.  Both
 * arguments must point to a context_t structure describing the saved
 * callee-saved registers and stack pointer.  The caller must preserve
 * caller-saved registers according to the System V ABI.  On return,
 * execution resumes on the context pointed to by *old.
 */

// Context definition moved to proc.h to avoid redefinition
// The context64 struct is defined in proc.h for all architectures
#ifndef EXO_CONTEXT_T
#define EXO_CONTEXT_T
// Using forward declaration - actual definition is in proc.h
struct context64;
typedef struct context64 context_t;
#endif /* EXO_CONTEXT_T */

void swtch(context_t **old, context_t *new);
static inline void cap_yield(context_t **old, context_t *target) {
  swtch(old, target);
}

int exo_yield_to(exo_cap target);
