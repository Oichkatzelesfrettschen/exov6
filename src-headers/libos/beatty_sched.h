#pragma once
#include "types.h"
#include "exo.h"

struct exo_sched_ops;
void beatty_sched_set_tasks(exo_cap a, exo_cap b);
void beatty_sched_init(void);
struct exo_sched_ops *beatty_sched_ops(void);
