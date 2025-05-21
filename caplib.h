#pragma once
#include "exo.h"
#include "exo_cpu.h"
#include "include/exokernel.h"

exo_cap cap_alloc_page(void);
int cap_unbind_page(exo_cap cap);
int cap_alloc_block(uint dev, exo_blockcap *cap);
int cap_bind_block(exo_blockcap *cap, void *data, int write);
int cap_flush_block(exo_blockcap *cap, void *data);
int cap_send(exo_cap dest, const void *buf, uint64 len);
int cap_recv(exo_cap src, void *buf, uint64 len);
int cap_set_timer(void (*handler)(void));
int cap_set_gas(uint64 amount);
int cap_get_gas(void);
void cap_yield_to(context_t **old, context_t *target);
int cap_yield_to_cap(exo_cap target);
int cap_read_disk(exo_blockcap cap, void *dst, uint64 off, uint64 n);
int cap_write_disk(exo_blockcap cap, const void *src, uint64 off, uint64 n);
int cap_send(exo_cap dest, const void *buf, uint64 len);
int cap_recv(exo_cap src, void *buf, uint64 len);
int cap_ipc_echo_demo(void);
int cap_send(exo_cap dest, const void *buf, uint64 len);
int cap_recv(exo_cap src, void *buf, uint64 len);
