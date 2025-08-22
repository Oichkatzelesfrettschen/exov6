#include "caplib.h"
#include "types.h"
#include "user.h"

exo_cap cap_alloc_page(void) { return exo_alloc_page(); }

EXO_NODISCARD int cap_unbind_page(exo_cap cap) { return exo_unbind_page(cap); }

EXO_NODISCARD int cap_alloc_block(uint32_t dev, uint32_t rights,
                                  exo_blockcap *cap) {
  return exo_alloc_block(dev, rights, cap);
}

EXO_NODISCARD int cap_bind_block(exo_blockcap *cap, void *data, int write) {
  return exo_bind_block(cap, data, write);
}

void cap_flush_block(exo_blockcap *cap, void *data) {
  exo_flush_block(cap, data);
}

EXO_NODISCARD int cap_set_timer(void (*handler)(void)) {
  return set_timer_upcall(handler);
}
EXO_NODISCARD int cap_set_gas(uint64_t amount) { return set_gas(amount); }
EXO_NODISCARD int cap_get_gas(void) { return get_gas(); }
EXO_NODISCARD int cap_out_of_gas(void) { return get_gas() <= 0; }

void cap_yield_to(context_t **old, context_t *target) {
  cap_yield(old, target);
}

EXO_NODISCARD int cap_yield_to_cap(exo_cap target) {
  return exo_yield_to(target);
}

EXO_NODISCARD int cap_read_disk(exo_blockcap cap, void *dst, uint64_t off,
                                uint64_t n) {
  return exo_read_disk(cap, dst, off, n);
}

EXO_NODISCARD int cap_write_disk(exo_blockcap cap, const void *src,
                                 uint64_t off, uint64_t n) {
  return exo_write_disk(cap, src, off, n);
}

extern int cap_revoke_syscall(uint16_t id);
int cap_revoke(uint16_t id) { return cap_revoke_syscall(id); }

EXO_NODISCARD int cap_send(exo_cap dest, const void *buf, uint64_t len) {
  return exo_send(dest, buf, len);
}

EXO_NODISCARD int cap_recv(exo_cap src, void *buf, uint64_t len) {
  return exo_recv(src, buf, len);
}

EXO_NODISCARD int cap_recv_timed(exo_cap src, void *buf, uint64_t len,
                                 unsigned timeout) {
  return exo_recv_timed(src, buf, len, timeout);
}

EXO_NODISCARD int cap_ipc_echo_demo(void) {
  const char *msg = "ping";
  char buf[5];
  exo_cap cap = {0, 0};

  int result = cap_send(cap, msg, 4);
  if (result != 0) {
    printf(2, "caplib echo: send failed\n");
    return result;
  }

  result = cap_recv(cap, buf, 4);
  if (result != 0) {
    printf(2, "caplib echo: recv failed\n");
    return result;
  }

  buf[4] = '\0';
  printf(1, "caplib echo: %s\n", buf);
  return 0;
}
