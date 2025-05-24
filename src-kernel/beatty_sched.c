#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "exo_stream.h"
#include "exo_cpu.h"
#include "math_core.h"

static struct spinlock beatty_lock;
static struct exo_sched_ops beatty_ops;
static struct exo_stream beatty_stream;

static exo_cap task_a;
static exo_cap task_b;
static uint64 na, nb;
static double alpha;
static double beta;

void beatty_sched_set_tasks(exo_cap a, exo_cap b) {
  acquire(&beatty_lock);
  task_a = a;
  task_b = b;
  na = 1;
  nb = 1;
  release(&beatty_lock);
}

static void beatty_halt(void) { /* nothing */ }

static void beatty_yield(void) {
  acquire(&beatty_lock);
  double va = alpha * (double)na;
  double vb = beta * (double)nb;
  exo_cap next;
  if ((uint64)va < (uint64)vb) {
    next = task_a;
    na++;
  } else {
    next = task_b;
    nb++;
  }
  release(&beatty_lock);

  if (next.pa)
    exo_yield_to(next);
}

void beatty_sched_init(void) {
  initlock(&beatty_lock, "beatty");
  alpha = phi();
  beta = alpha / (alpha - 1.0);
  beatty_ops.halt = beatty_halt;
  beatty_ops.yield = beatty_yield;
  beatty_ops.next = 0;
  beatty_stream.head = &beatty_ops;
  exo_stream_register(&beatty_stream);
}
