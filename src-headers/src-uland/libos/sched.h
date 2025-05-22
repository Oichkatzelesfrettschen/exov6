#pragma once
#include "types.h"
#include "caplib.h"

void sched_add(exo_cap cap);
void sched_install_timer(void);
void sched_run(void);

struct dag_node;

/* DAG scheduling helpers.  Nodes can be given a weight and
 * dependencies.  The simple user-space implementation orders ready
 * nodes by descending weight. */
struct dag_node_edge {
  struct dag_node *child;
  struct dag_node_edge *next;
};

struct dag_node {
  exo_cap ctx;
  int weight;
  int pending;
  int done;
  struct dag_node_edge *children;
  struct dag_node *next;
};

void dag_node_init(struct dag_node *n, exo_cap ctx);
void dag_node_set_weight(struct dag_node *n, int weight);
void dag_node_add_dep(struct dag_node *parent, struct dag_node *child);
void dag_sched_submit(struct dag_node *node);
void dag_sched_yield(void);
