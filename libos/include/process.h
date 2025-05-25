#pragma once
#include "user.h"

/* Simple process management helpers */

int proc_spawn(const char *path, char *const argv[]);
int proc_wait(int pid);
int proc_kill(int pid);

