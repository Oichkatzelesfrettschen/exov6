#include "types.h"
#include "defs.h"
#include "exo_stream.h"

/*
 * Combined Beatty and DAG scheduler stream.
 *
 * The kernel first initializes the individual scheduler modules
 * (dag_sched_init() and beatty_sched_init()) and then registers a
 * single exo stream that chains them together.  Beatty dispatches
 * according to its irrational weights and falls through to the DAG
 * scheduler when nodes become ready.  Call beatty_dag_stream_init()
 * early during boot before user tasks begin executing so that
 * libraries can submit DAG nodes and configure Beatty weights via
 * beatty_sched_set_tasks().
 */

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
