#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "exo_stream.h"
#include "exo_cpu.h"
#include "math_core.h"
#include "dag.h"

static struct spinlock beatty_lock;
static struct exo_sched_ops beatty_ops;
static struct exo_stream beatty_stream;

static exo_cap task_a;
static exo_cap task_b;
static uint64_t na, nb;
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
  if ((uint64_t)va < (uint64_t)vb) {
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
#ifdef HAVE_DECIMAL_FLOAT
  alpha = dec64_to_double(phi());
#else
  alpha = phi();
#endif
  beta = alpha / (alpha - 1.0);
  beatty_ops.halt = beatty_halt;
  beatty_ops.yield = beatty_yield;
  beatty_ops.next = 0;
  beatty_stream.head = &beatty_ops;
  exo_stream_register(&beatty_stream);
}

/** DFS helper for cycle detection when scheduling DAG nodes. */
static bool path_exists(struct dag_node *src, struct dag_node *dst,
                        struct dag_node **stack, size_t depth) {
  for (size_t i = 0; i < depth; ++i)
    if (stack[i] == src)
      return false;
  if (src == dst)
    return true;
  stack[depth] = src;
  for (struct dag_node_list *l = src->children; l; l = l->next)
    if (path_exists(l->node, dst, stack, depth + 1))
      return true;
  return false;
}

/** Check whether scheduling @p n would introduce a cycle. */
static bool creates_cycle(struct dag_node *n) {
  struct dag_node *stack[64];
  for (int i = 0; i < n->ndeps; ++i)
    if (path_exists(n->deps[i], n, stack, 0))
      return true;
  return false;
}

/**
 * Submit a DAG node under the Beatty scheduler.
 *
 * Returns ``-1`` if the submission would create a cycle.
 */
int dag_sched_submit(struct dag_node *n) {
  acquire(&beatty_lock);
  if (creates_cycle(n)) {
    release(&beatty_lock);
    return -1;
  }
  if (n->pending == 0 && !n->done)
    n->next = 0; /* ready list unused in Beatty scheduler */
  release(&beatty_lock);
  return 0;
}
