#include "types.h"
#include "user.h"
#include "chan.h"
#include "capnp_helpers.h"
#include "math_core.h"
#include "libos/driver.h"

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

CHAN_DECLARE_VAR(ping_chan, VarMsg);

static ping_chan_t *c;
static double alpha;
static double beta;
static int na = 1;
static int nb = 1;
static int child;

static void send_task(int slice) {
    VarMsg m = { .len = 1, .data = { (char)('0' + slice) } };
    exo_cap cap = {0};
    ping_chan_send(c, cap, &m);
    printf(1, "sent %c\n", m.data[0]);
}

static void recv_task(void) {
    VarMsg out = {0};
    exo_cap cap = {0};
    ping_chan_recv(c, cap, &out);
    printf(1, "received %s\n", out.data);
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
#ifdef HAVE_DECIMAL_FLOAT
    alpha = dec64_to_double(phi());
#else
    alpha = phi();
#endif
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
    exit(0);
}
