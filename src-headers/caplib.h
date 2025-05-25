#pragma once
#include "exo.h"
#include "exo_cpu.h"
#include "exokernel.h"

exo_cap cap_alloc_page(void);
[[nodiscard]] int cap_unbind_page(exo_cap cap);
[[nodiscard]] int cap_alloc_block(uint32_t dev, uint32_t rights, exo_blockcap *cap);
[[nodiscard]] int cap_bind_block(exo_blockcap *cap, void *data, int write);
void cap_flush_block(exo_blockcap *cap, void *data);
[[nodiscard]] int cap_send(exo_cap dest, const void *buf, uint64_t len);
[[nodiscard]] int cap_recv(exo_cap src, void *buf, uint64_t len);
[[nodiscard]] int cap_set_timer(void (*handler)(void));
[[nodiscard]] int cap_set_gas(uint64_t amount);
[[nodiscard]] int cap_get_gas(void);
[[nodiscard]] int cap_out_of_gas(void);
void cap_yield_to(context_t **old, context_t *target);
[[nodiscard]] int cap_yield_to_cap(exo_cap target);
[[nodiscard]] int cap_read_disk(exo_blockcap cap, void *dst, uint64_t off,
                                uint64_t n);
[[nodiscard]] int cap_write_disk(exo_blockcap cap, const void *src, uint64_t off,
                                 uint64_t n);
[[nodiscard]] int cap_ipc_echo_demo(void);
[[nodiscard]] int cap_inc(uint16_t id);
[[nodiscard]] int cap_dec(uint16_t id);
