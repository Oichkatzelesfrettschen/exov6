#include "libos.h"
#include "stat.h"
#include "types.h"
#include "user.h"

int main(void) {
  void *va = 0;
  exo_cap cap = libos_page_alloc(&va);
  if (!cap.pa) {
    printf(1, "alloc failed\n");
    exit();
  }
  char *p = (char *)va;
  p[0] = 'L';
  p[1] = 'O';
  p[2] = 'S';
  p[3] = '\n';
  write(1, p, 4);
  libos_sched_yield(cap); // just yields
  libos_page_free(cap, va);
  exit();
}
