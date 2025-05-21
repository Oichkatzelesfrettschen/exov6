#include "types.h"
#include "user.h"
#include "chan.h"

struct ping_msg {
    int value;
};

CHAN_DECLARE(ping_chan, struct ping_msg);

int
main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    ping_chan_t *c = ping_chan_create();
    struct ping_msg m = { 7 };
    exo_cap cap = {0};
    ping_chan_send(c, cap, &m);
    ping_chan_destroy(c);
    exit();
}

