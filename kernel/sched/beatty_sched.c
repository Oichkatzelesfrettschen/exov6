#include <types.h>
#include "defs.h"
#include "spinlock.h"
#include "exo_lock.h"  /* Modern qspinlock */
#include "exo_stream.h"
#include "exo_cpu.h"
#include "q16_fixed.h"  /* Use Q16.16 fixed-point instead of math_core.h */
#include "dag.h"

static struct qspinlock beatty_lock;
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

/* Use Q16.16 fixed-point for Beatty sequences */
static q16_t alpha;  /* First irrational (golden ratio) */
static q16_t beta;   /* Second irrational (1/(1-1/φ)) */

void beatty_sched_set_tasks(exo_cap a, exo_cap b) {
  qspin_lock(&beatty_lock);
  task_a = a;
  task_b = b;
  na = 1;
  nb = 1;
  qspin_unlock(&beatty_lock);
}

static void beatty_halt(void) { /* nothing */ }

static void beatty_yield(void) {
  qspin_lock(&beatty_lock);
  
  /* Calculate Beatty sequence values using Q16.16 */
  uint32_t beatty_a = q16_beatty(na, alpha);
  uint32_t beatty_b = q16_beatty(nb, beta);
  
  exo_cap next;
  if (beatty_a < beatty_b) {
    next = task_a;
    na++;
  } else {
    next = task_b;
    nb++;
  }
  qspin_unlock(&beatty_lock);

  if (next.pa)
    /* Yield operation in scheduler context; errors are not critical */
    (void)exo_yield_to(next);
}

void beatty_sched_init(void) {
  qspin_init(&beatty_lock, "beatty", LOCK_LEVEL_SCHEDULER);
  
  /* Initialize golden ratio and its complement for Beatty sequences */
  alpha = Q16_PHI;  /* φ = 1.618... */
  
  /* Calculate β = φ/(φ-1) = φ² for complementary Beatty sequence */
  /* Since φ² = φ + 1, we can compute: β = φ + 1 */
  beta = q16_add(Q16_PHI, Q16_ONE);  /* β ≈ 2.618... */
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
  qspin_lock(&beatty_lock);
  if (creates_cycle(n)) {
    qspin_unlock(&beatty_lock);
    return -1;
  }
  if (n->pending == 0 && !n->done)
    n->next = 0; /* ready list unused in Beatty scheduler */
  qspin_unlock(&beatty_lock);
  return 0;
}
