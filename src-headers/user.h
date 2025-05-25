#pragma once
#include <sys/types.h>

int exec(char *path, char **argv);
int sigsend(int pid, int sig);
int sigcheck(void);
