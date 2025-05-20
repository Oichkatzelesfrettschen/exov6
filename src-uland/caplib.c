#include "caplib.h"
#include "types.h"
#include "user.h"

exo_cap cap_alloc_page(void) {
  exo_cap c;
  exo_alloc_page(&c);
  return c;
}

int cap_unbind_page(exo_cap cap) { return exo_unbind_page(cap); }

int cap_alloc_block(uint dev, exo_blockcap *cap) {
  return exo_alloc_block(dev, cap);
}

int cap_bind_block(exo_blockcap *cap, void *data, int write) {
  return exo_bind_block(cap, data, write);
}

int cap_flush_block(exo_blockcap *cap, void *data) {
  return exo_flush_block(cap, data);
}

int cap_set_timer(void (*handler)(void)) { return set_timer_upcall(handler); }

void cap_yield_to(context_t **old, context_t *target) {
  cap_yield(old, target);
}

int cap_yield_to_cap(exo_cap target) { return exo_yield_to(&target); }

int cap_read_disk(exo_blockcap cap, void *dst, uint64 off, uint64 n) {
  return exo_read_disk(cap, dst, off, n);
}

int cap_write_disk(exo_blockcap cap, const void *src, uint64 off, uint64 n) {
  return exo_write_disk(cap, src, off, n);
}

int cap_send(exo_cap dest, const void *buf, uint64 len) {
  return exo_send(&dest, buf, len);
}

int cap_recv(exo_cap src, void *buf, uint64 len) {
  return exo_recv(&src, buf, len);
}

int cap_ipc_echo_demo(void) {
  const char *msg = "ping";
  char buf[5];
  exo_cap cap = {0, 0};
  cap_send(cap, msg, 4);
  cap_recv(cap, buf, 4);
  buf[4] = '\0';
  printf(1, "caplib echo: %s\n", buf);
  return 0;
}
