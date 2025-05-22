#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "exo_stream.h"
#include "kernel/exo_cpu.h"
#include "math_core.h"

static struct spinlock beatty_lock;
static struct exo_sched_ops beatty_ops;
static struct exo_stream beatty_stream;

static exo_cap task_a;
static exo_cap task_b;
static uint64 na, nb;
static double alpha;
static double beta;
static int weight_a = 1;
static int weight_b = 1;

void beatty_sched_set_tasks(exo_cap a, exo_cap b) {
  acquire(&beatty_lock);
  task_a = a;
  task_b = b;
  na = 1;
  nb = 1;
  release(&beatty_lock);
}

void beatty_sched_set_weights(int wa, int wb) {
  if (wa <= 0)
    wa = 1;
  if (wb <= 0)
    wb = 1;
  acquire(&beatty_lock);
  weight_a = wa;
  weight_b = wb;
  na = 1;
  nb = 1;
  alpha = (double)(wa + wb) / (double)wa;
  beta = (double)(wa + wb) / (double)wb;
  release(&beatty_lock);
}

static int beatty_pick(void) {
  double va = alpha * (double)na;
  double vb = beta * (double)nb;
  int ret;
  if ((uint64)va < (uint64)vb) {
    na++;
    ret = 0;
  } else {
    nb++;
    ret = 1;
  }
  return ret;
}

static void beatty_halt(void) { /* nothing */ }

static void beatty_yield(void) {
  acquire(&beatty_lock);
  exo_cap next = beatty_pick() == 0 ? task_a : task_b;
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
  beatty_ops.next = dag_sched_get_ops();
  beatty_stream.head = &beatty_ops;
  exo_stream_register(&beatty_stream);
}

struct exo_sched_ops *beatty_sched_ops(void) { return &beatty_ops; }
