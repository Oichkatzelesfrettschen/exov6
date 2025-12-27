/**
 * @file beatty_dag_demo.c
 * @brief Standalone Beatty sequence + DAG scheduler demonstration
 *
 * This demo demonstrates the Beatty sequence scheduling algorithm
 * combined with DAG task organization, using local stubs to avoid
 * kernel dependencies.
 *
 * Beatty sequences partition the natural numbers using irrational
 * coefficients. With alpha = phi (golden ratio) and beta = phi/(phi-1),
 * we get two complementary sequences that never overlap.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <math.h>

/* ═══════════════════════════════════════════════════════════════════════
 * LOCAL STUBS - Standalone demo without kernel dependencies
 * ═══════════════════════════════════════════════════════════════════════ */

/* Local capability stub */
typedef struct demo_cap { uint32_t id; } demo_cap;

/* Local DAG node stub */
struct demo_dag_node {
    const char *name;
    int pending;
    int priority;
};

/* Scheduler state stubs */
static void demo_dag_sched_init(void) {
    printf("[sched] DAG scheduler initialized\n");
}

static void demo_beatty_sched_init(void) {
    printf("[sched] Beatty scheduler initialized\n");
}

static void demo_dag_node_init(struct demo_dag_node *n, demo_cap ctx) {
    (void)ctx;
    n->pending = 0;
    n->priority = 0;
}

static void demo_dag_sched_submit(struct demo_dag_node *n) {
    printf("[sched] Submitted task: %s\n", n->name);
}

static void demo_exo_stream_yield(void) {
    /* No-op in standalone demo */
}

/* ═══════════════════════════════════════════════════════════════════════
 * BEATTY SEQUENCE SCHEDULER
 * ═══════════════════════════════════════════════════════════════════════ */

/* Golden ratio constant */
static double phi(void) {
    return (1.0 + sqrt(5.0)) / 2.0;
}

static double alpha;
static double beta;
static int na = 1;
static int nb = 1;

/* Simple task node with linked-list for family chains */
struct simple_node {
    const char *name;
    struct simple_node *next;
};

static struct simple_node a1 = {"A1", NULL};
static struct simple_node a2 = {"A2", NULL};
static struct simple_node b1 = {"B1", NULL};
static struct simple_node b2 = {"B2", NULL};

static struct simple_node *afam = &a1;
static struct simple_node *bfam = &b1;

static void run_family(struct simple_node **head) {
    if (*head) {
        printf("[run] Executing task: %s\n", (*head)->name);
        *head = (*head)->next;
    }
}

/**
 * schedule_step - Execute one scheduling step using Beatty sequences
 *
 * The Beatty sequence property ensures fair interleaving:
 * - floor(alpha * n) and floor(beta * n) partition the naturals
 * - When alpha = phi, beta = phi/(phi-1) ≈ 2.618
 */
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
    demo_exo_stream_yield();
}

/* ═══════════════════════════════════════════════════════════════════════
 * MAIN DEMONSTRATION
 * ═══════════════════════════════════════════════════════════════════════ */

int main(int argc, char *argv[]) {
    (void)argc; (void)argv;

    /* Initialize Beatty sequence parameters */
    alpha = phi();
    beta = alpha / (alpha - 1.0);

    printf("═══════════════════════════════════════════════════════════\n");
    printf("Beatty DAG Scheduler Demo\n");
    printf("═══════════════════════════════════════════════════════════\n");
    printf("alpha (phi)     = %.6f\n", alpha);
    printf("beta (phi/phi-1) = %.6f\n", beta);
    printf("Note: alpha + beta = alpha * beta = %.6f\n", alpha * beta);
    printf("═══════════════════════════════════════════════════════════\n\n");

    /* Build simple DAG chains */
    a1.next = &a2;
    b1.next = &b2;

    /* Initialize schedulers */
    demo_dag_sched_init();
    demo_beatty_sched_init();

    /* Initialize DAG nodes */
    struct demo_dag_node da1 = {.name = "A1"};
    struct demo_dag_node da2 = {.name = "A2"};
    struct demo_dag_node db1 = {.name = "B1"};
    struct demo_dag_node db2 = {.name = "B2"};

    demo_dag_node_init(&da1, (demo_cap){0});
    demo_dag_node_init(&da2, (demo_cap){0});
    demo_dag_node_init(&db1, (demo_cap){0});
    demo_dag_node_init(&db2, (demo_cap){0});

    /* Submit tasks to DAG scheduler */
    demo_dag_sched_submit(&da1);
    demo_dag_sched_submit(&da2);
    demo_dag_sched_submit(&db1);
    demo_dag_sched_submit(&db2);

    printf("\n[demo] Starting Beatty sequence scheduling...\n\n");

    /* Run scheduling steps - Beatty sequence determines execution order */
    for (int i = 0; i < 4; i++) {
        printf("[step %d] ", i + 1);
        schedule_step();
    }

    printf("\n═══════════════════════════════════════════════════════════\n");
    printf("Beatty DAG demo complete\n");
    printf("═══════════════════════════════════════════════════════════\n");

    return 0;
}
