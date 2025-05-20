#pragma once
#include "types.h"
#include "exo.h"

struct dag_node;

struct dag_node_list {
  struct dag_node *node;
  struct dag_node_list *next;
};

struct dag_node {
  exo_cap ctx;
  int pending;
  struct dag_node_list *children;
  struct dag_node *next;
};

void dag_node_init(struct dag_node *n, exo_cap ctx);
void dag_node_add_dep(struct dag_node *parent, struct dag_node *child);
void dag_sched_submit(struct dag_node *node);
void dag_sched_init(void);
