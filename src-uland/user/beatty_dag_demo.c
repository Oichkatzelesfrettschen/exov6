#include "types.h"
#include "user.h"
#include "math_core.h"
#include "libos/dag.h"
#include "libos/beatty_sched.h"
#include "libos/sched.h"

static double alpha;
static double beta;
static int na = 1;
static int nb = 1;

struct simple_node {
    const char *name;
    struct simple_node *next;
};

static struct simple_node a1 = {"A1", 0};
static struct simple_node a2 = {"A2", 0};
static struct simple_node b1 = {"B1", 0};
static struct simple_node b2 = {"B2", 0};

static struct simple_node *afam = &a1;
static struct simple_node *bfam = &b1;

static void run_family(struct simple_node **head) {
    if (*head) {
        printf(1, "%s\n", (*head)->name);
        *head = (*head)->next;
    }
}

static void schedule_step(void) {
    double va = alpha * (double)na;
    double vb = beta * (double)nb;
    if ((int)va < (int)vb) {
        run_family(&afam);
        na++;
    } else {
        run_family(&bfam);
        nb++;
    }
    exo_stream_yield();
}

int main(int argc, char *argv[]) {
    (void)argc; (void)argv;
    alpha = phi();
    beta = alpha / (alpha - 1.0);

    // build simple DAGs
    a1.next = &a2;
    b1.next = &b2;

    dag_sched_init();
    beatty_sched_init();

    dag_node_init((struct dag_node *)&a1, (exo_cap){0});
    dag_node_init((struct dag_node *)&a2, (exo_cap){0});
    dag_node_init((struct dag_node *)&b1, (exo_cap){0});
    dag_node_init((struct dag_node *)&b2, (exo_cap){0});

    dag_sched_submit((struct dag_node *)&a1);
    dag_sched_submit((struct dag_node *)&a2);
    dag_sched_submit((struct dag_node *)&b1);
    dag_sched_submit((struct dag_node *)&b2);

    printf(1, "beatty_dag_demo start\n");
    for (int i = 0; i < 4; i++)
        schedule_step();
    printf(1, "beatty_dag_demo done\n");
    exit();
}
