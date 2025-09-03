#pragma once
#include <types.h>
#include "caplib.h"

[[nodiscard]] int driver_spawn(const char *path, char *const argv[]);
[[nodiscard]] int driver_connect(int pid, exo_cap ep);
