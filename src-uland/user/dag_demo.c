#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct exo_cap { uint32_t pa; } exo_cap;

struct dag_node { int pending; };

static void dag_node_init(struct dag_node *n, exo_cap ctx) {
  (void)ctx; n->pending = 0;
}
static void dag_node_add_dep(struct dag_node *parent, struct dag_node *child) {
  (void)parent; (void)child;
}
static void dag_sched_submit(struct dag_node *node) {
  (void)node; printf("dag_sched_submit\n");
}
static void exo_stream_yield(void) {
  printf("exo_stream_yield called\n");
}

static struct dag_node a, b, c;

static void setup(void) {
  exo_cap cap = {0};
  dag_node_init(&a, cap);
  dag_node_init(&b, cap);
  dag_node_init(&c, cap);
  dag_node_add_dep(&a, &c);
  dag_node_add_dep(&b, &c);
  dag_sched_submit(&a);
  dag_sched_submit(&b);
  dag_sched_submit(&c);
}

int main(int argc, char *argv[]) {
  (void)argc; (void)argv;
  printf("DAG scheduler demo\n");
  setup();
  exo_stream_yield();
  return 0;
}
