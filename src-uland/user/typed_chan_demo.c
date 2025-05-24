#include "types.h"
#include "user.h"
#include "chan.h"
#include "proto/driver.capnp.h"

CHAN_DECLARE(ping_chan, DriverPing);

int
main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    ping_chan_t *c = ping_chan_create();
    DriverPing msg = { .value = 123 };
    exo_cap cap = {0};
    ping_chan_send(c, cap, &msg);
    DriverPing out = {0};
    ping_chan_recv(c, cap, &out);
    printf(1, "typed channel message %d\n", out.value);

    // Demonstrate failure when message sizes do not match
    char bad[1] = {0};
    int r = chan_endpoint_send(&c->base, cap, bad, sizeof(bad));
    printf(1, "bad send result %d\n", r);
    r = chan_endpoint_recv(&c->base, cap, bad, sizeof(bad));
    printf(1, "bad recv result %d\n", r);

    // Correct usage again
    ping_chan_send(c, cap, &msg);
    memset(&out, 0, sizeof(out));
    ping_chan_recv(c, cap, &out);
    printf(1, "typed channel message %d\n", out.value);
    ping_chan_destroy(c);
    exit();
}
