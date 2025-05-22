#pragma once
#include "types.h"
#include "user.h"
#include "caplib.h"

void sched_add(exo_cap cap);
void sched_install_timer(void);
void sched_run(void);
