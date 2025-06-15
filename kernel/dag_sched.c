#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "dag.h"
#include "lattice_ipc.h"
#include "exo_stream.h"
#include "exo_cpu.h"
#include <string.h>

static struct spinlock dag_lock;
static struct dag_node *ready_head;

static struct exo_sched_ops dag_ops;
static struct exo_stream dag_stream;

/** Determine scheduling weight based on node priority. */
static inline int node_weight(struct dag_node *n) { return n->priority; }

/** Initialize a DAG node. */
void dag_node_init(struct dag_node *n, exo_cap ctx) {
  memset(n, 0, sizeof(*n));
  n->ctx = ctx;
  n->chan = NULL;
}

/** Set the scheduling priority of a node. */
void dag_node_set_priority(struct dag_node *n, int priority) {
  n->priority = priority;
}

/** Attach a lattice IPC channel used for yielding. */
void dag_node_set_channel(struct dag_node *n, lattice_channel_t *chan) {
  n->chan = chan;
}

/**
 * Register @p child as dependent on @p parent.
 */
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

/** Run the next ready node and yield to its context. */
static void dag_yield(void) {
  struct dag_node *n;

  acquire(&dag_lock);
  n = dequeue_ready();
  release(&dag_lock);

  if (!n)
    return;

  if (n->chan)
    lattice_yield_to(n->chan);
  else
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
