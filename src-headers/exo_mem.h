#pragma once
<<<<<<<< HEAD:src-headers/exo_mem.h
#include "exo.h"
========
#include "../../exo.h"
>>>>>>>> fd61ec6 (Restructure sources into src-kernel and src-uland):src-kernel/kernel/exo_mem.h

exo_cap exo_alloc_page(void);
int exo_unbind_page(exo_cap cap);
