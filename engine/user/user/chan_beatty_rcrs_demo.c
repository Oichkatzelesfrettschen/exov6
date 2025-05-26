#include "types.h"
#include "user.h"
#include "chan.h"
#include "capnp_helpers.h"
#include "math_core.h"
#include "libos/driver.h"
#include "proto/driver.capnp.h"

CHAN_DECLARE(ping_chan, DriverPing);

static ping_chan_t *c;
static double alpha;
static double beta;
static int na = 1;
static int nb = 1;
static int child;

static void send_task(int slice) {
    DriverPing m = { .value = slice };
    exo_cap cap = {0};
    ping_chan_send(c, cap, &m);
    printf(1, "sent %d\n", slice);
}

static void recv_task(void) {
    DriverPing out = {0};
    exo_cap cap = {0};
    ping_chan_recv(c, cap, &out);
    printf(1, "received %d\n", out.value);
}

static void schedule_step(int slice) {
    double va = alpha * (double)na;
    double vb = beta * (double)nb;
    if ((int)va < (int)vb) {
        send_task(slice);
        na++;
    } else {
        recv_task();
        nb++;
    }
}

int main(int argc, char *argv[]) {
    (void)argc; (void)argv;
    char *rargv[] = {"typed_chan_recv", 0};
    child = driver_spawn("typed_chan_recv", rargv);

    c = ping_chan_create();
    alpha = phi();
    beta = alpha / (alpha - 1.0);

    for (int i = 1; i <= 4; i++) {
        if (i == 3) {
            printf(1, "simulating rcrs restart\n");
            kill(child);
            wait();
            child = driver_spawn("typed_chan_recv", rargv);
        }
        schedule_step(i);
    }

    kill(child);
    wait();
    ping_chan_destroy(c);
    exit();
}
