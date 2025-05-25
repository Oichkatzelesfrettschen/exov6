#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include_next <sched.h>
#include "dag.h"

void libos_setup_beatty_dag(void);

#ifdef __cplusplus
}
#endif
