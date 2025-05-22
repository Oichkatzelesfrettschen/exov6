#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "dag.h"
#include "exo_stream.h"
#include "kernel/exo_cpu.h"


static struct spinlock dag_lock;
static struct dag_node *ready_head;

static struct exo_sched_ops dag_ops;
static struct exo_stream dag_stream;

void
dag_node_init(struct dag_node *n, exo_cap ctx)
{
  memset(n, 0, sizeof(*n));
  n->ctx = ctx;
  n->weight = 1;
}

void
dag_node_set_priority(struct dag_node *n, int priority)
{
  n->priority = priority;
}

void
dag_node_set_weight(struct dag_node *n, int weight)
{
  n->weight = weight > 0 ? weight : 1;
}

void
dag_node_add_dep(struct dag_node *parent, struct dag_node *child)
{
  struct dag_node_list *l = (struct dag_node_list *)kalloc();
  if(!l)
    return;
  l->node = child;
  l->next = parent->children;
  parent->children = l;
  child->pending++;
}

static void
enqueue_ready(struct dag_node *n)
{
  struct dag_node **pp = &ready_head;
  int prio = n->priority * n->weight;
  while(*pp && ((*pp)->priority * (*pp)->weight) >= prio)
    pp = &(*pp)->next;
  n->next = *pp;
  *pp = n;
}

void
dag_sched_submit(struct dag_node *n)
{
  acquire(&dag_lock);
  if(n->pending == 0)
    enqueue_ready(n);
  release(&dag_lock);
}

static struct dag_node *
dequeue_ready(void)
{
  struct dag_node *n = ready_head;
  if(n)
    ready_head = n->next;
  return n;
}

static void
dag_mark_done(struct dag_node *n)
{
  struct dag_node_list *l;
  for(l = n->children; l; l = l->next){
    struct dag_node *child = l->node;
    if(--child->pending == 0)
      enqueue_ready(child);
  }
}

static void
dag_yield(void)
{
  struct dag_node *a, *b = 0;

  acquire(&dag_lock);
  a = dequeue_ready();
  if(a)
    b = dequeue_ready();
  release(&dag_lock);

  if(!a)
    return;

  if(!b){
    exo_yield_to(a->ctx);
    acquire(&dag_lock);
    dag_mark_done(a);
    release(&dag_lock);
    return;
  }

  beatty_sched_set_tasks(a->ctx, b->ctx);
  beatty_sched_set_weights(a->weight, b->weight);
  int pick = beatty_sched_pick();
  struct dag_node *run = pick == 0 ? a : b;
  struct dag_node *rest = pick == 0 ? b : a;

  exo_yield_to(run->ctx);

  acquire(&dag_lock);
  dag_mark_done(run);
  enqueue_ready(rest);
  release(&dag_lock);
}

static void
dag_halt(void)
{
  // nothing
}

void
dag_sched_init(void)
{
  initlock(&dag_lock, "dag");
  dag_ops.halt = dag_halt;
  dag_ops.yield = dag_yield;
  dag_ops.next = 0;
  dag_stream.head = &dag_ops;
}

struct exo_sched_ops *dag_sched_get_ops(void)
{
  return &dag_ops;
}

