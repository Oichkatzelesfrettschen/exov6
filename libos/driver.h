#pragma once
#include "types.h"
#include "caplib.h"

int driver_spawn(const char *path, char *const argv[]);
int driver_connect(int pid, exo_cap ep);
