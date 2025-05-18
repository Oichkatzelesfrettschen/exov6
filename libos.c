#include "libos.h"

// Allocate a page and bind it to a freshly expanded address
exo_cap libos_page_alloc(void **va) {
  exo_cap cap = exo_alloc_page();
  if (!cap.pa)
    return cap;
  void *addr = sbrk(4096);
  if ((long)addr == -1) {
    exo_unbind_page(cap);
    cap.pa = 0;
    return cap;
  }
  if (exo_bind_page(cap, addr, PTE_W | PTE_U) < 0) {
    exo_unbind_page(cap);
    cap.pa = 0;
    return cap;
  }
  *va = addr;
  return cap;
}

int libos_page_free(exo_cap cap, void *va) {
  (void)va; // mapping removed by exo_unbind_page
  return exo_unbind_page(cap);
}

int libos_sched_yield(exo_cap target) { return exo_yield_to(target); }

int libos_disk_read(int fd, void *dst, int n) { return read(fd, dst, n); }

int libos_disk_write(int fd, const void *src, int n) {
  return write(fd, src, n);
}
