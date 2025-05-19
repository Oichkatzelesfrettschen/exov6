#pragma once
#include "../../exo.h"

exo_cap exo_alloc_page(void);
int exo_unbind_page(exo_cap cap);
