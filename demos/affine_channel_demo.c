#include "types.h"
#include "user.h"
#include "affine_runtime.h"
#include "capnp_helpers.h"
#include "driver.capnp.h"

AFFINE_CHAN_DECLARE(aff_ping_chan, DriverPing);

int
main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    aff_ping_chan_t *c = aff_ping_chan_create();
    DriverPing m = { .value = 77 };
    exo_cap cap = {0};

    int r = aff_ping_chan_send(c, cap, &m);
    printf(1, "first send %d\n", r);

    r = aff_ping_chan_send(c, cap, &m);
    printf(1, "second send %d\n", r);

    aff_ping_chan_destroy(c);
    exit(0);
}
