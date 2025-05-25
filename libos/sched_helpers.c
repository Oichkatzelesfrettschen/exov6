#include "libos/sched.h"
#include "libos/dag.h"
#include "libos/beatty_sched.h"
#include "user.h"

void libos_setup_beatty_dag(void) {
  // Initialize user-space schedulers and select the combined stream.
  dag_sched_init();
  beatty_sched_init();
  beatty_dag_stream_init();
}
