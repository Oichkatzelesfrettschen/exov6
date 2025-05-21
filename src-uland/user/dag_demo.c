#include "caplib.h"
#include "types.h"
#include "user.h"
#include "dag.h"

// Stub exo_yield_to since kernel support is unavailable
int exo_yield_to(exo_cap target) {
  printf(1, "exo_yield_to called with cap %p\n", (void *)target.pa);
  return 0;
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
  printf(1, "DAG scheduler demo\n");
  setup();
  exo_stream_yield();
  exit();
}
