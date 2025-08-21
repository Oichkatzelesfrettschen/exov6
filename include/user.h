#pragma once
#include "types.h"
#include "exo.h"

/* Prevent conflicts with system headers */
#ifndef PHOENIX_USER_H_DECLS
#define PHOENIX_USER_H_DECLS

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

/* System calls not declared elsewhere */
int set_timer_upcall(void (*handler)(void));
int set_gas(uint64_t amount);
int get_gas(void);
void exo_flush_block(exo_blockcap *cap, void *data);

/* Basic syscalls */
void *sbrk(int nbytes);
int write(int fd, const void *buf, int count);

#endif /* PHOENIX_USER_H_DECLS */
