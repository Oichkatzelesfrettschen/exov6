#include "src-uland/libos/sched.h"
#include <stdio.h>
#include <stdlib.h>

#define MAX_PROCS 64

static exo_cap runq[MAX_PROCS];
static int nprocs = 0;
static int cur = -1;
#define GAS_SLICE 5

void sched_add(exo_cap cap) {
  if (nprocs < MAX_PROCS)
    runq[nprocs++] = cap;
}

static void sched_tick(void) {
  if (nprocs == 0)
    return;
  if (!cap_out_of_gas())
    return;
  for (int i = 0; i < nprocs; i++) {
    cur = (cur + 1) % nprocs;
    cap_set_gas(GAS_SLICE);
    cap_yield_to_cap(runq[cur]);
    if (!cap_out_of_gas())
      break;
  }
}

void sched_install_timer(void) { cap_set_timer(sched_tick); }

void sched_run(void) {
  sched_install_timer();
  if (nprocs > 0) {
    cur = 0;
    cap_set_gas(GAS_SLICE);
    cap_yield_to_cap(runq[cur]);
  }
  while (1)
    sched_tick();
}

/* ------------------------- DAG scheduler ------------------------- */

static struct dag_node *ready_head;

static void enqueue_ready(struct dag_node *n) {
  struct dag_node **pp = &ready_head;
  while (*pp && (*pp)->weight >= n->weight)
    pp = &(*pp)->next;
  n->next = *pp;
  *pp = n;
}

void dag_node_init(struct dag_node *n, exo_cap ctx) {
  n->ctx = ctx;
  n->weight = 0;
  n->pending = 0;
  n->done = 0;
  n->children = 0;
  n->next = 0;
}

void dag_node_set_weight(struct dag_node *n, int weight) { n->weight = weight; }

void dag_node_add_dep(struct dag_node *parent, struct dag_node *child) {
  struct dag_node_edge *e = malloc(sizeof(*e));
  if (!e)
    return;
  e->child = child;
  e->next = parent->children;
  parent->children = e;
  child->pending++;
}

void dag_sched_submit(struct dag_node *n) {
  if (n->pending == 0 && !n->done)
    enqueue_ready(n);
}

void dag_sched_yield(void) {
  struct dag_node *n = ready_head;
  if (!n) {
    printf("dag_sched_yield: no runnable nodes\n");
    return;
  }
  ready_head = n->next;

  printf("running node weight %d\n", n->weight);

  n->done = 1;
  struct dag_node_edge *e = n->children;
  while (e) {
    struct dag_node *child = e->child;
    if (--child->pending == 0 && !child->done)
      enqueue_ready(child);
    e = e->next;
  }
}
