/* Demo showing how to compose lambda policies with IRQ events */
#include "libos/affine_runtime.h"
#include "libos/irq_client.h"
#include "types.h"
#include "user.h"

/* Simple environment shared by the policies */
typedef struct {
    exo_cap irq_cap;
    int remaining;
} irq_env_t;

/* Wait for an IRQ and report its number. */
static int policy_wait(void *arg) {
    irq_env_t *env = arg;
    unsigned n = 0;
    if (irq_wait(env->irq_cap, &n) < 0)
        return -1; /* keep waiting */
    printf(1, "received IRQ %u\n", n);
    return 1; /* move to next policy */
}

/* Acknowledge the IRQ and decrement the counter. */
static int policy_ack(void *arg) {
    irq_env_t *env = arg;
    irq_ack(env->irq_cap);
    env->remaining--;
    return env->remaining ? 1 : -1; /* stop after final ack */
}

/* Compose two lambda policies sequentially. */
static int run_seq(void *arg) {
    lambda_term_t *terms = arg;
    int r = lambda_run(&terms[0], 1);
    if (r != 0)
        r = lambda_run(&terms[1], 1);
    return r;
}

int
main(void)
{
    exo_cap cap = exo_alloc_irq(5, EXO_RIGHT_R | EXO_RIGHT_W);
    irq_env_t env = { cap, 3 };

    lambda_term_t steps[] = {
        { policy_wait, &env, 0 },
        { policy_ack, &env, 0 }
    };
    lambda_term_t seq = { run_seq, steps, 0 };

    while (lambda_run(&seq, 1) == 0)
        ;
    return 0;
}
