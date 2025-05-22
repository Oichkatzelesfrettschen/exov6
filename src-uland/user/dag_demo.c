#include <stdio.h>
#include "src-uland/libos/sched.h"

static struct dag_node a, b, c;

static void setup(void) {
  exo_cap cap = {0};
  dag_node_init(&a, cap);
  dag_node_set_weight(&a, 10);
  dag_node_init(&b, cap);
  dag_node_set_weight(&b, 5);
  dag_node_init(&c, cap);
  dag_node_set_weight(&c, 1);
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
  dag_sched_yield();
  dag_sched_yield();
  dag_sched_yield();
  return 0;
}
