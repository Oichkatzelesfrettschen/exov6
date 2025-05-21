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

static int demo_yield_to(exo_cap target) {
    printf(1, "exo_yield_to %p\n", (void*)target.pa);
    return 0;
}

void dag_submit(struct dag_node *list) {
    printf(1, "dag_submit called\n");
    while (1) {
        struct dag_node *n, *ready = 0;
        for (n = list; n; n = n->next) {
            if (n->done) continue;
            int i;
            for (i = 0; i < n->ndeps; i++)
                if (!n->deps[i]->done)
                    break;
            if (i == n->ndeps) { ready = n; break; }
        }
        if (!ready) break;
        demo_yield_to(ready->ctx);
        ready->done = 1;
        printf(1, "node %p done\n", ready);
    }
}

int main(int argc, char **argv) {
    struct dag_node a, b, c;
    struct dag_node *deps_b[] = { &a };
    struct dag_node *deps_c[] = { &b };
    a.ctx.pa = 1; a.deps = 0; a.ndeps = 0; a.done = 0; a.next = &b;
    b.ctx.pa = 2; b.deps = deps_b; b.ndeps = 1; b.done = 0; b.next = &c;
    c.ctx.pa = 3; c.deps = deps_c; c.ndeps = 1; c.done = 0; c.next = 0;
    dag_submit(&a);
    exit();

}
