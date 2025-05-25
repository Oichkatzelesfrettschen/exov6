#pragma once
#include "types.h"

int proc_spawn(const char *path, char *const argv[]);
int proc_wait(int pid);
int proc_kill(int pid);
