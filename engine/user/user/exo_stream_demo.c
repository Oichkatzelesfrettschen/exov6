#include <stdio.h>
#include <stdint.h>
#include "spinlock.h"
#include "exo_stream.h"
#include "defs.h"

typedef struct exo_cap {
  uint32_t pa;
  uint32_t id;
} exo_cap;

// Minimal stub implementations used when kernel support is absent.
int exo_yield_to(exo_cap *target) {
  printf("exo_yield_to called with cap %u\n", target->id);
  return 0;
}

// Simple user-level demonstration for exo_yield_to
int exo_yield_to_demo(exo_cap target) {
  printf(1, "exo_yield_to called with cap %p\n", (void *)target.id);
  return 0;
}

static struct spinlock streams_lock;

/*
 * Stop processing the current STREAMS pipeline. Release any held lock and
 * wake the scheduler so resources can be reclaimed.
 */
void streams_stop(void) {
  if (streams_lock.name)
    release(&streams_lock);
  exo_stream_halt();
  yield();
}

/*
 * Yield execution of the current STREAMS module. The lock guarding the
 * stream state is released before returning control to the scheduler.
 */
void streams_yield(void) {
  if (streams_lock.name)
    release(&streams_lock);
  exo_stream_yield();
  yield();
}

int main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  exo_cap other = {0, 42};
  exo_yield_to(&other);
  exo_yield_to_demo(other);
  streams_yield();
  streams_stop();
  return 0;
}
