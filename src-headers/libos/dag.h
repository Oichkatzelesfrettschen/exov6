#pragma once
#include "../dag.h"

struct exo_sched_ops;
void dag_sched_init(void);
struct exo_sched_ops *dag_sched_ops(void);
