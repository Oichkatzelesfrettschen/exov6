#include "types.h"
#include "user.h"
#include "unified_chan.h"

typedef struct {
    uint8_t len;
    char data[8];
} VarMsg;

static size_t VarMsg_encode(const VarMsg *m, unsigned char *buf) {
    if(buf){
        buf[0] = m->len;
        for(size_t i=0;i<m->len;i++)
            buf[1+i] = m->data[i];
    }
    return 1 + m->len;
}

static size_t VarMsg_decode(VarMsg *m, const unsigned char *buf) {
    m->len = buf[0];
    for(size_t i=0;i<m->len;i++)
        m->data[i] = buf[1+i];
    m->data[m->len] = '\0';
    return 1 + m->len;
}

#define VarMsg_MESSAGE_SIZE 9

/* Now CHAN_DECLARE_VAR is provided by unified system */
CHAN_DECLARE_VAR(ping_chan, VarMsg);

int
main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    ping_chan_t *c = ping_chan_create();
    VarMsg msg = { .len = 5, .data = "hello" };
    exo_cap cap = {0};
    ping_chan_send(c, cap, &msg);
    VarMsg out = {0};
    ping_chan_recv(c, cap, &out);
    printf(1, "variable message: %s\n", out.data);

    msg.len = 3;
    msg.data[0] = 'b'; msg.data[1] = 'y'; msg.data[2] = 'e';
    ping_chan_send(c, cap, &msg);
    memset(&out, 0, sizeof(out));
    ping_chan_recv(c, cap, &out);
    printf(1, "variable message: %s\n", out.data);
    ping_chan_destroy(c);
    exit();
}
