#include "types.h"
#include "user.h"
#include "chan.h"
#include "capnp_helpers.h"
#include "dag.h"
#include "libos/driver.h"
#include "proto/driver.capnp.h"

CHAN_DECLARE(ping_chan, DriverPing);

static ping_chan_t *c;
static struct dag_node send_node, recv_node;

static void send_task(void)
{
    DriverPing m = { .value = 42 };
    exo_cap cap = {0};
    ping_chan_send(c, cap, &m);
    printf(1, "sent ping\n");
}

static void recv_task(void)
{
    DriverPing out = {0};
    exo_cap cap = {0};
    ping_chan_recv(c, cap, &out);
    printf(1, "received %d\n", out.value);
}

int main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    char *rargv[] = {"typed_chan_recv", 0};
    int pid = driver_spawn("typed_chan_recv", rargv);

    dag_sched_init();
    c = ping_chan_create();

    dag_node_init(&send_node, (exo_cap){0});
    dag_node_init(&recv_node, (exo_cap){0});
    dag_node_add_dep(&send_node, &recv_node);

    dag_sched_submit(&send_node);
    dag_sched_submit(&recv_node);

    send_task();
    recv_task();
    exo_stream_yield();

    kill(pid);
    wait();

    ping_chan_destroy(c);
    exit();
}
