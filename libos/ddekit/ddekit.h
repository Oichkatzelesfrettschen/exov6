#pragma once
#include "include/capwrap.h"
#include "include/process.h"

/* Minimal DDEKit wrapper for Phoenix */

int ddekit_init(void);
int ddekit_start_driver(const char *path, char *const argv[], exo_cap *drv_ep);
int ddekit_handoff_cap(exo_cap ep, exo_cap cap);
