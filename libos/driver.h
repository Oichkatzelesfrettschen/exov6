#pragma once
#include "types.h"
#include "caplib.h"

<<<<<<< Updated upstream:libos/driver.h
<<<<<<< Updated upstream:libos/driver.h
EXO_NODISCARD int driver_spawn(const char *path, char *const argv[]);
EXO_NODISCARD int driver_connect(int pid, exo_cap ep);
=======
[[nodiscard]] int driver_spawn(const char *path, char *const argv[]);
[[nodiscard]] int driver_connect(int pid, exo_cap ep);
>>>>>>> Stashed changes:engine/libos/driver.h
=======
[[nodiscard]] int driver_spawn(const char *path, char *const argv[]);
[[nodiscard]] int driver_connect(int pid, exo_cap ep);
>>>>>>> Stashed changes:engine/libos/driver.h
