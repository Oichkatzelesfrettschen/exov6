#include "caplib.h"
#include "types.h"
#include "user.h"


// Simplified STREAMS API stubs
void streams_stop(void) { printf(1, "streams_stop called\n"); }

void streams_yield(void) { printf(1, "streams_yield called\n"); }

int main(int argc, char *argv[]) {
  exo_cap cap = {0};
  printf(1, "STREAMS/exo yield demo\n");
  streams_stop();
  exo_yield_to(cap);
  streams_yield();
  exit();
}
