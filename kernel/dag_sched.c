#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "dag.h"
#include "exo_stream.h"
#include "exo_cpu.h"
#include <string.h>

static struct spinlock dag_lock;
static struct dag_node *ready_head;
#define DAG_MAX_DEPTH 64

static struct exo_sched_ops dag_ops;
static struct exo_stream dag_stream;

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

static inline int node_weight(struct dag_node *n) { return n->priority; }

void dag_node_init(struct dag_node *n, exo_cap ctx) {
  memset(n, 0, sizeof(*n));
  n->ctx = ctx;
}

void dag_node_set_priority(struct dag_node *n, int priority) {
  n->priority = priority;
}

void dag_node_add_dep(struct dag_node *parent, struct dag_node *child) {
  struct dag_node_list *l = (struct dag_node_list *)kalloc();
  if (!l)
    return;
  l->node = child;
  l->next = parent->children;
  parent->children = l;
  child->pending++;
  if (child->deps == 0)
    child->deps = (struct dag_node **)kalloc();
  if (child->deps)
    child->deps[child->ndeps++] = parent;
}

int dag_add_edge(struct dag_node *parent, struct dag_node *child) {
  acquire(&dag_lock);
  if (path_exists(child, parent)) {
    release(&dag_lock);
    return -1;
  }
  dag_node_add_dep(parent, child);
  release(&dag_lock);
  return 0;
}

/**
 * @brief Insert a ready node ordered by priority.
 */
static void enqueue_ready(struct dag_node *n) {
  int w = node_weight(n);
  struct dag_node **pp = &ready_head;
  while (*pp && node_weight(*pp) >= w)

    pp = &(*pp)->next;
  n->next = *pp;
  *pp = n;
}

/** DFS helper for cycle detection. */
static bool dfs_path(struct dag_node *src, struct dag_node *dst,
                     struct node_vec *stack, struct node_vec *visited) {
  if (contains(stack, src))
    return true; /* back-edge */
  if (contains(visited, src))
    return false;
  if (!push(stack, src))
    return true; /* depth limit */
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

int dag_sched_submit(struct dag_node *n) {
  acquire(&dag_lock);
  if (creates_cycle(n)) {
    release(&dag_lock);
    return -1;
  }
  if (n->pending == 0 && !n->done)
    enqueue_ready(n);
  release(&dag_lock);
  return 0;
}

static struct dag_node *dequeue_ready(void) {
  struct dag_node *n = ready_head;
  if (n)
    ready_head = n->next;
  return n;
}

static void dag_mark_done(struct dag_node *n) {
  struct dag_node_list *l;
  n->done = 1;
  for (l = n->children; l; l = l->next) {

    struct dag_node *child = l->node;
    if (--child->pending == 0)
      enqueue_ready(child);
  }
}

static void dag_yield(void) {
  struct dag_node *n;

  acquire(&dag_lock);
  n = dequeue_ready();
  release(&dag_lock);

  if (!n)
    return;

  exo_yield_to(n->ctx);

  acquire(&dag_lock);
  dag_mark_done(n);
  release(&dag_lock);
}

void dag_yield_to(struct dag_node *n) {
  if (!n)
    return;

  acquire(&dag_lock);
  if (n->pending > 0 || n->done) {
    release(&dag_lock);
    return;
  }
  release(&dag_lock);

  exo_yield_to(n->ctx);

  acquire(&dag_lock);
  dag_mark_done(n);
  release(&dag_lock);
}

static void dag_halt(void) {
  // nothing
}

void dag_sched_init(void) {
  initlock(&dag_lock, "dag");
  dag_ops.halt = dag_halt;
  dag_ops.yield = dag_yield;
  dag_ops.next = 0;
  dag_stream.head = &dag_ops;
  exo_stream_register(&dag_stream);
}
