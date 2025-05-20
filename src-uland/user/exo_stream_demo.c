#include "caplib.h"
#include "types.h"
#include "user.h"

// Stub function since kernel support is unavailable
int exo_yield_to(exo_cap *target) {
  printf(1, "exo_yield_to called with cap %p\n", (void *)target->id);
  return 0;
}

// Simplified STREAMS API stubs
void streams_stop(void) { printf(1, "streams_stop called\n"); }

void streams_yield(void) { printf(1, "streams_yield called\n"); }

int main(int argc, char *argv[]) {
  exo_cap cap = {0};
  printf(1, "STREAMS/exo yield demo\n");
  streams_stop();
  exo_yield_to(&cap);
  streams_yield();
  exit();
}
