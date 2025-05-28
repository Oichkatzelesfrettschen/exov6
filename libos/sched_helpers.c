#include "libos/sched.h"
#include "dag.h"
#include "user.h"
#include "defs.h"

void libos_setup_beatty_dag(void) {
  // Initialize two schedulers already configured in the kernel
  // and select the combined Beatty+DAG stream.
  beatty_dag_stream_init();
}
