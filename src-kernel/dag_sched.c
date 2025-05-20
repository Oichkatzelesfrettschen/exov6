#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "dag.h"
#include "exo_stream.h"
#include "exo_cpu.h"

static struct spinlock dag_lock;
static struct dag_node *ready_head;

static struct exo_sched_ops dag_ops;
static struct exo_stream dag_stream;

void
dag_node_init(struct dag_node *n, exo_cap ctx)
{
  memset(n, 0, sizeof(*n));
  n->ctx = ctx;
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
  n->next = ready_head;
  ready_head = n;
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
  struct dag_node *n;

  acquire(&dag_lock);
  n = dequeue_ready();
  release(&dag_lock);

  if(!n)
    return;

  exo_yield_to(n->ctx);

  acquire(&dag_lock);
  dag_mark_done(n);
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
  exo_stream_register(&dag_stream);
}
