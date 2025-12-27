/**
 * @file exo_stream_demo.c
 * @brief Standalone ExoStream demonstration
 *
 * This demo shows the exo_yield_to and stream control primitives.
 * Uses local stubs for standalone host builds.
 */
#include <stdio.h>
#include <stdint.h>

/* Local capability stub - avoids kernel header dependencies */
typedef struct demo_cap {
  uint32_t pa;
  uint32_t id;
} demo_cap;

/* Stub for exo_yield_to - just demonstrates the call */
static int demo_yield_to(demo_cap *target) {
  printf("demo_yield_to called with cap id=%u\n", target->id);
  return 0;
}

/* Stub for streams_stop */
static void demo_streams_stop(void) {
  printf("demo_streams_stop called\n");
}

/* Stub for streams_yield */
static void demo_streams_yield(void) {
  printf("demo_streams_yield called\n");
}

int main(int argc, char **argv) {
  (void)argc;
  (void)argv;

  printf("=== ExoStream Demo ===\n");

  demo_cap other = {0, 42};
  printf("Created capability with id=%u\n", other.id);

  demo_yield_to(&other);
  demo_streams_yield();
  demo_streams_stop();

  printf("=== Demo Complete ===\n");
  return 0;
}
