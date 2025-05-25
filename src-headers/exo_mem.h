#pragma once
#include "libos/exo-userland.h"

exo_cap exo_alloc_page(void);
[[nodiscard]] int exo_unbind_page(exo_cap cap);
