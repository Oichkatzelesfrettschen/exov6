#include <types.h>
#include "spinlock.h"
#include "defs.h"
#include "exo_stream.h"
#include "streams.h"

/*
 * Simple placeholder STREAMS runtime. A real implementation would
 * manage a pipeline of modules exchanging message blocks. The
 * current prototype only records whether the pipeline remains
 * runnable when the scheduler calls into the stream callbacks.
 */

struct streams_state {
  int runnable;
};

static struct streams_state sstate;
static struct spinlock streams_lock;
static struct exo_sched_ops streams_ops;
static struct exo_stream streams;

void streams_sched_init(void) {
  initlock(&streams_lock, "streams");
  streams_ops.halt = streams_stop;
  streams_ops.yield = streams_yield;
  streams_ops.next = 0;
  streams.head = &streams_ops;
  exo_stream_register(&streams);
}

void streams_stop(void) {
  acquire(&streams_lock);
  /* Flush outstanding messages and mark pipeline inactive. */
  sstate.runnable = 0;
  release(&streams_lock);
}

void streams_yield(void) {
  acquire(&streams_lock);
  /* Save module state and mark runnable so the scheduler can resume us. */
  sstate.runnable = 1;
  release(&streams_lock);
}
