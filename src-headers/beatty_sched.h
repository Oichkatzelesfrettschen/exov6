#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include "types.h"
#include "exo.h"

void beatty_sched_set_tasks(const exo_cap *tasks, const double *weights, int n);
void beatty_sched_init(void);
#ifdef __cplusplus
}
#endif
