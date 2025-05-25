#pragma once
#include "types.h"
#include "caplib.h"

[[nodiscard]] int driver_spawn(const char *path, char *const argv[]);
[[nodiscard]] enum exo_ipc_status driver_connect(int pid, exo_cap ep);
