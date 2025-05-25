#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include "libos/sched.h"
#include "streams.h"

typedef struct exo_cap {
  uint32_t pa;
} exo_cap;

struct dag_node {
  int pending;
  int priority;
};

static void dag_node_init(struct dag_node *n, exo_cap ctx) {
  (void)ctx;
  n->pending = 0;
  n->priority = 0;
}
static void dag_node_add_dep(struct dag_node *parent, struct dag_node *child) {
  (void)parent;
  (void)child;
}
static void dag_sched_submit(struct dag_node *node) {
  printf("dag_sched_submit priority %d\n", node->priority);
}

static struct dag_node a, b, c;

static void setup(void) {
  exo_cap cap = {0};
  dag_node_init(&a, cap);
  dag_node_set_priority(&a, 10);
  dag_node_init(&b, cap);
  dag_node_set_priority(&b, 5);
  dag_node_init(&c, cap);
  dag_node_set_priority(&c, 1);
  dag_node_add_dep(&a, &c);
  dag_node_add_dep(&b, &c);
  dag_sched_submit(&a);
  dag_sched_submit(&b);
  dag_sched_submit(&c);
}

int main(int argc, char *argv[]) {
  (void)argc;
  (void)argv;
  printf("DAG scheduler demo\n");
  setup();
  streams_yield();
  streams_yield();
  streams_yield();
  return 0;
}
