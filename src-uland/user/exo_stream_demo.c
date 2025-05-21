#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct exo_cap {
  uint32_t pa;
  uint32_t id;
} exo_cap;

// Minimal stub implementations used when kernel support is absent.
static int exo_yield_to_demo(exo_cap target) {
  printf("exo_yield_to called with cap %p\n", (void *)target.pa);
  return 0;
}

int exo_yield_to(exo_cap *target) {
  printf("exo_yield_to called with cap %u\n", target->id);
  return 0;
}

void streams_stop(void) { printf("streams_stop called\n"); }
void streams_yield(void) { printf("streams_yield called\n"); }

int main(int argc, char *argv[]) {
  exo_cap cap = {0, 0};
  printf("STREAMS/exo yield demo\n");
  streams_stop();
  exo_yield_to_demo(cap);
  exo_yield_to(&cap);
  streams_yield();
  return 0;
}
