#include "types.h"
#include "user.h"
#include "chan.h"
#include "libos/driver.h"
#include "proto/driver.capnp.h"

CHAN_DECLARE(ping_chan, DriverPing);

static ping_chan_t *c;

static void send_task(void)
{
    DriverPing m = { .value = 73 };
    exo_cap cap = {0};
    ping_chan_send(c, cap, &m);
    printf(1, "beatty send\n");
}

static void recv_task(void)
{
    DriverPing out = {0};
    exo_cap cap = {0};
    ping_chan_recv(c, cap, &out);
    printf(1, "beatty recv %d\n", out.value);
}

int
main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    char *rargv[] = {"typed_chan_recv", 0};
    int pid = driver_spawn("typed_chan_recv", rargv);

    c = ping_chan_create();

    beatty_sched_set_tasks((exo_cap){0}, (exo_cap){0});

    send_task();
    exo_stream_yield();
    recv_task();
    exo_stream_yield();

    kill(pid);
    wait();

    ping_chan_destroy(c);
    exit();
}
