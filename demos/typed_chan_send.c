#include "types.h"
#include "user.h"
#include "chan.h"
#include "capnp_helpers.h"
#include "proto/driver.capnp.h"

CHAN_DECLARE(ping_chan, DriverPing);

int
main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    ping_chan_t *c = ping_chan_create();
    DriverPing m = { .value = 7 };
    exo_cap cap = {0};
    ping_chan_send(c, cap, &m);
    ping_chan_destroy(c);
    exit();
}
