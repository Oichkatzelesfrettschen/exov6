#pragma once

/**
 * @file sched.h
 * @brief LibOS scheduler interface
 */

#include "dag.h"

void libos_setup_beatty_dag(void);
int libos_sched_init(void);
void libos_sched_yield(void);