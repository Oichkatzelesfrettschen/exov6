#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include "libos/sched.h"

typedef struct exo_cap { uint32_t pa; } exo_cap;

struct dag_node { int pending; int priority; int weight; };

static void dag_node_init(struct dag_node *n, exo_cap ctx) {
  (void)ctx;
  n->pending = 0;
  n->priority = 0;
  n->weight = 1;
}
static void dag_node_add_dep(struct dag_node *parent, struct dag_node *child) {
  (void)parent; (void)child;
}
static void dag_sched_submit(struct dag_node *node) {
  printf("dag_sched_submit prio %d weight %d\n", node->priority, node->weight);
}
static void exo_stream_yield(void) {
  printf("exo_stream_yield called\n");
}
static void beatty_sched_set_tasks(exo_cap a, exo_cap b) {
  (void)a; (void)b; printf("beatty_sched_set_tasks called\n");
}
static void beatty_sched_set_weights(int a, int b) {
  printf("beatty_sched_set_weights %d %d\n", a, b);
}

static struct dag_node a, b, c;

static void setup(void) {
  exo_cap cap = {0};
  dag_node_init(&a, cap);
  dag_node_set_priority(&a, 10);
  dag_node_set_weight(&a, 3);
  dag_node_init(&b, cap);
  dag_node_set_priority(&b, 5);
  dag_node_set_weight(&b, 1);
  dag_node_init(&c, cap);
  dag_node_set_priority(&c, 1);
  dag_node_set_weight(&c, 2);
  dag_node_add_dep(&a, &c);
  dag_node_add_dep(&b, &c);
  dag_sched_submit(&a);
  dag_sched_submit(&b);
  dag_sched_submit(&c);
  beatty_sched_set_tasks(cap, cap);
  beatty_sched_set_weights(3, 1);
}

int main(int argc, char *argv[]) {
  (void)argc; (void)argv;
  printf("DAG scheduler demo\n");
  setup();
  exo_stream_yield();
  exo_stream_yield();
  exo_stream_yield();
  return 0;
}
