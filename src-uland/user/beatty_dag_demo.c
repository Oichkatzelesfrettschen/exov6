#include <stdio.h>
#include "libos/sched.h"

/* Minimal stubs when kernel support is missing */
struct dag_node {
  int pending;
  int priority;
  struct dag_node *next;
};
static void dag_node_init(struct dag_node *n) {
  n->pending = 0;
  n->priority = 0;
}
static void dag_node_add_dep(struct dag_node *p, struct dag_node *c) {
  (void)p;
  (void)c;
}
static void dag_sched_submit(struct dag_node *n) {
  printf("submit node prio %d\n", n->priority);
}
static void beatty_sched_set_tasks(int a, int b) {
  (void)a;
  (void)b;
  printf("beatty tasks set\n");
}
static void exo_stream_yield(void) { printf("yield via combined stream\n"); }

int main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  struct dag_node a1, a2, b1, b2;
  dag_node_init(&a1);
  dag_node_init(&a2);
  dag_node_init(&b1);
  dag_node_init(&b2);
  dag_node_add_dep(&a1, &a2);
  dag_node_add_dep(&b1, &b2);
  dag_sched_submit(&a1);
  dag_sched_submit(&a2);
  dag_sched_submit(&b1);
  dag_sched_submit(&b2);

  libos_setup_beatty_dag();
  exo_stream_yield();
  exo_stream_yield();
  exo_stream_yield();
  return 0;
}
