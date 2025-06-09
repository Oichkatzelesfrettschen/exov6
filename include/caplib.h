#pragma once
#include "exo.h"
#include "exo_cpu.h"
#include "exokernel.h"

exo_cap cap_alloc_page(void);
EXO_NODISCARD int cap_unbind_page(exo_cap cap);
EXO_NODISCARD int cap_alloc_block(uint32_t dev, uint32_t rights,
                                  exo_blockcap *cap);
EXO_NODISCARD int cap_bind_block(exo_blockcap *cap, void *data, int write);
void cap_flush_block(exo_blockcap *cap, void *data);
EXO_NODISCARD int cap_send(exo_cap dest, const void *buf, uint64_t len);
EXO_NODISCARD int cap_recv(exo_cap src, void *buf, uint64_t len);
EXO_NODISCARD int cap_recv_timed(exo_cap src, void *buf, uint64_t len,
                                 unsigned timeout);
EXO_NODISCARD int cap_set_timer(void (*handler)(void));
EXO_NODISCARD int cap_set_gas(uint64_t amount);
EXO_NODISCARD int cap_get_gas(void);
EXO_NODISCARD int cap_out_of_gas(void);
void cap_yield_to(context_t **old, context_t *target);
EXO_NODISCARD int cap_yield_to_cap(exo_cap target);
EXO_NODISCARD int cap_read_disk(exo_blockcap cap, void *dst, uint64_t off,
                                uint64_t n);
EXO_NODISCARD int cap_write_disk(exo_blockcap cap, const void *src,
                                 uint64_t off, uint64_t n);
EXO_NODISCARD int cap_ipc_echo_demo(void);
EXO_NODISCARD int cap_inc(uint16_t id);
EXO_NODISCARD int cap_dec(uint16_t id);
