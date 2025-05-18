#pragma once
#include "../exo.h"

exo_cap exo_alloc_page(void);
int exo_bind_page(exo_cap cap, void *va, int perm);
int exo_unbind_page(exo_cap cap);
