#ifndef LIBOS_H
#define LIBOS_H
#include "user.h"

exo_cap libos_page_alloc(void **va);
int libos_page_free(exo_cap cap, void *va);
int libos_sched_yield(exo_cap target);
int libos_disk_read(int fd, void *dst, int n);
int libos_disk_write(int fd, const void *src, int n);

#endif // LIBOS_H
