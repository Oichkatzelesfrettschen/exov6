#pragma once
#include "types.h"

#ifdef __cplusplus
extern "C" {
#endif

int proc_spawn(const char *path, char *const argv[]);
int proc_wait(int pid);
int proc_kill(int pid);

#ifdef __cplusplus
}
#endif
