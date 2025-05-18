#pragma once
#include <stdint.h>

typedef uint64_t cap_t;

cap_t exo_alloc_page(void);
int exo_bind_page(cap_t cap, void *va, int perm);
int exo_unbind_page(void *va);
