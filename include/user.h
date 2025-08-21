#pragma once
#include "types.h"

int exec(char *path, char **argv);
int sigsend(int pid, int sig);
int sigcheck(void);

/* User-space library functions */
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wincompatible-library-redeclaration"
void printf(int fd, const char *fmt, ...);
#pragma clang diagnostic pop

void *malloc(size_t size);
void free(void *ptr);
