#include "types.h"
#include "defs.h"
#include "exo_stream.h"

static struct exo_stream beatty_dag_stream;

void beatty_dag_stream_init(void) {
  // initialize underlying schedulers
  dag_sched_init();
  beatty_sched_init();

  struct exo_sched_ops *beatty = beatty_sched_ops();
  struct exo_sched_ops *dag = dag_sched_ops();

  beatty->next = dag;
  dag->next = 0;
  beatty_dag_stream.head = beatty;
  exo_stream_register(&beatty_dag_stream);
}
