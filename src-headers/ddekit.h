#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include "types.h"
#include "caplib.h"

struct ddekit_process {
  int pid;
};

void ddekit_init(void);
int ddekit_process_spawn(struct ddekit_process *p, const char *path,
                         char *const argv[]);
int ddekit_process_wait(struct ddekit_process *p);
void ddekit_process_exit(int code) __attribute__((noreturn));
void ddekit_yield(void);

exo_cap ddekit_cap_alloc_page(void);
int ddekit_cap_send(exo_cap dest, const void *buf, size_t len);
int ddekit_cap_recv(exo_cap src, void *buf, size_t len);
#ifdef __cplusplus
}
#endif
