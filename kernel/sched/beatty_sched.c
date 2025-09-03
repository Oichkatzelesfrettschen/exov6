#include <types.h>
#include "defs.h"
#include "spinlock.h"
#include "exo_stream.h"
#include "exo_cpu.h"
#include "math_core.h"
#include "dag.h"

static struct spinlock beatty_lock;
static struct exo_sched_ops beatty_ops;
static struct exo_stream beatty_stream;

#define DAG_MAX_DEPTH 64
struct node_vec {
  struct dag_node **data;
  size_t len;
};

static bool contains(struct node_vec *v, struct dag_node *n) {
  for (size_t i = 0; i < v->len; ++i)
    if (v->data[i] == n)
      return true;
  return false;
}

static bool push(struct node_vec *v, struct dag_node *n) {
  if (v->len >= DAG_MAX_DEPTH)
    return false;
  v->data[v->len++] = n;
  return true;
}

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
static bool dfs_path(struct dag_node *src, struct dag_node *dst,
                     struct node_vec *stack, struct node_vec *visited) {
  if (contains(stack, src))
    return true;
  if (contains(visited, src))
    return false;
  if (!push(stack, src))
    return true;
  push(visited, src);
  if (src == dst)
    return true;
  for (struct dag_node_list *l = src->children; l; l = l->next)
    if (dfs_path(l->node, dst, stack, visited))
      return true;
  stack->len--;
  return false;
}

static bool path_exists(struct dag_node *src, struct dag_node *dst) {
  struct dag_node *stack_buf[DAG_MAX_DEPTH];
  struct dag_node *visit_buf[DAG_MAX_DEPTH];
  struct node_vec stack = {stack_buf, 0};
  struct node_vec visited = {visit_buf, 0};
  return dfs_path(src, dst, &stack, &visited);
}

/** Check whether scheduling @p n would introduce a cycle. */
static bool creates_cycle(struct dag_node *n) {
  for (int i = 0; i < n->ndeps; ++i)
    if (path_exists(n->deps[i], n))
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
