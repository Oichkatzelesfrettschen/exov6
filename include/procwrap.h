#pragma once
#include <stddef.h>
#include "types.h"

#ifndef EXO_NORETURN
#define EXO_NORETURN __attribute__((noreturn))
#endif

typedef struct {
  int pid;
} proc_handle_t;

int proc_spawn(proc_handle_t *p, const char *path, char *const argv[]);
int proc_wait(proc_handle_t *p);
void proc_exit(int code) EXO_NORETURN;
