#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "dag.h"
#include "exo_stream.h"
#include "kernel/exo_cpu.h"
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

#include "dag.h"
#include "defs.h"
#include "spinlock.h"
#include "exo_stream.h"

static struct dag_node *dag_list;
static struct spinlock dag_lock;

static struct dag_node *find_ready(void) {
    struct dag_node *n;
    for (n = dag_list; n; n = n->next) {
        if (n->done)
            continue;
        int i;
        for (i = 0; i < n->ndeps; i++)
            if (!n->deps[i]->done)
                break;
        if (i == n->ndeps)
            return n;
    }
    return 0;
}

static void run_ready(void) {
    struct dag_node *n;
    acquire(&dag_lock);
    n = find_ready();
    release(&dag_lock);
    if (!n)
        return;
    exo_yield_to(n->ctx);
    acquire(&dag_lock);
    n->done = 1;
    release(&dag_lock);
}

static void dag_yield(void) { run_ready(); }
static void dag_halt(void) { run_ready(); }

static struct exo_sched_ops dag_ops = {
    .halt = dag_halt,
    .yield = dag_yield,
    .next = 0,
};

void dag_sched_init(struct exo_stream *stream) {
    initlock(&dag_lock, "dag");
    dag_ops.next = stream->head;
    stream->head = &dag_ops;
}

void dag_submit(struct dag_node *list) {
    acquire(&dag_lock);
    if (!dag_list)
        dag_list = list;
    else {
        struct dag_node *t = dag_list;
        while (t->next)
            t = t->next;
        t->next = list;
    }
    for (struct dag_node *n = list; n; n = n->next)
        n->done = 0;
    release(&dag_lock);

