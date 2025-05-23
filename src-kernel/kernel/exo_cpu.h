#pragma once
#include "types.h"
#include "exo.h"
#include "proc.h"

#if defined(__x86_64__) || defined(__aarch64__)
typedef struct context64 context_t;
#else
typedef struct context context_t;
#endif

void swtch(context_t **old, context_t *new);
int exo_yield_to(exo_cap target);
