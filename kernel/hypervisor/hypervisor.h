#pragma once
#include "exo.h"

exo_cap exo_alloc_hypervisor(void);
int hv_launch_guest(exo_cap cap, const char *path);
