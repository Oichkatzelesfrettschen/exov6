#pragma once
#include "types.h"
#include "caplib.h"

EXO_NODISCARD int driver_spawn(const char *path, char *const argv[]);
EXO_NODISCARD int driver_connect(int pid, exo_cap ep);
