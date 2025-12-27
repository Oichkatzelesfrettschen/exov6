/**
 * @file dag_demo.c
 * @brief Standalone DAG scheduler demonstration
 *
 * This demo uses local stubs to demonstrate DAG scheduling concepts
 * without depending on kernel headers.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

/* Local capability stub - standalone demo */
typedef struct demo_cap { uint32_t pa; } demo_cap;

/* Local DAG node stub - standalone demo */
struct demo_dag_node { int pending; int priority; };

static void demo_dag_node_init(struct demo_dag_node *n, demo_cap ctx) {
  (void)ctx; n->pending = 0; n->priority = 0;
}
static void demo_dag_node_set_priority(struct demo_dag_node *n, int priority) {
  n->priority = priority;
}
static void demo_dag_node_add_dep(struct demo_dag_node *parent, struct demo_dag_node *child) {
  (void)parent; (void)child;
}
static void demo_dag_sched_submit(struct demo_dag_node *node) {
  printf("dag_sched_submit priority %d\n", node->priority);
}
static void demo_exo_stream_yield(void) {
  printf("exo_stream_yield called\n");
}

static struct demo_dag_node a, b, c;

static void setup(void) {
  demo_cap cap = {0};
  demo_dag_node_init(&a, cap);
  demo_dag_node_set_priority(&a, 10);
  demo_dag_node_init(&b, cap);
  demo_dag_node_set_priority(&b, 5);
  demo_dag_node_init(&c, cap);
  demo_dag_node_set_priority(&c, 1);
  demo_dag_node_add_dep(&a, &c);
  demo_dag_node_add_dep(&b, &c);
  demo_dag_sched_submit(&a);
  demo_dag_sched_submit(&b);
  demo_dag_sched_submit(&c);
}

int main(int argc, char *argv[]) {
  (void)argc; (void)argv;
  printf("DAG scheduler demo\n");
  setup();
  demo_exo_stream_yield();
  demo_exo_stream_yield();
  demo_exo_stream_yield();
  return 0;
}
