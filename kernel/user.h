#pragma once
#include <sys/types.h>

int exec(const char *path, char *const argv[]);  /* Match defs.h signature */
int sigsend(int pid, int sig);
int sigcheck(void);
