#include "caplib.h"
#include "types.h"
#include "user.h"

exo_cap cap_alloc_page(void) { return exo_alloc_page(); }

int cap_unbind_page(exo_cap cap) { return exo_unbind_page(cap); }

int cap_alloc_block(uint dev, exo_blockcap *cap) {
  return exo_alloc_block(dev, cap);
}

int cap_bind_block(exo_blockcap *cap, void *data, int write) {
  return exo_bind_block(cap, data, write);
}

int cap_set_timer(void (*handler)(void)) { return set_timer_upcall(handler); }

void cap_yield_to(context_t **old, context_t *target) {
  cap_yield(old, target);
}

int cap_yield_to_cap(exo_cap target) { return exo_yield_to(target); }

int cap_read_disk(exo_blockcap cap, void *dst, uint64 off, uint64 n) {
  return exo_read_disk(cap, dst, off, n);
}

int cap_write_disk(exo_blockcap cap, const void *src, uint64 off, uint64 n) {
  return exo_write_disk(cap, src, off, n);
}
