#ifndef _DDEKIT_DDEKIT_H
#define _DDEKIT_DDEKIT_H

#include <stddef.h>
#include <stdint.h>

// Include capwrap to get exo_cap definition
#include <capwrap.h>

struct ddekit_process {
  int pid;
};

void ddekit_init(void);
int ddekit_process_spawn(struct ddekit_process *p, const char *path,
                         char *const argv[]);
int ddekit_process_wait(struct ddekit_process *p);
void ddekit_process_exit(int code);
void ddekit_yield(void);

exo_cap ddekit_cap_alloc_page(void);
int ddekit_cap_send(exo_cap dest, const void *buf, size_t len);
int ddekit_cap_recv(exo_cap src, void *buf, size_t len);

#endif
