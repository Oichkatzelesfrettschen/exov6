#include "exokernel.h"
#include "exo_ipc.h"
#include "ipc.h"
#include "uv_spinlock.h"
#include <string.h>
#include <errno.h>

#define IPC_BUFSZ 64

struct ipc_entry {
    zipc_msg_t msg;
    exo_cap frame;
};

static struct {
    uv_spinlock_t lock;
    struct ipc_entry buf[IPC_BUFSZ];
    unsigned r, w;
    int inited;
} ipcs;

static void ipc_init(void) {
    if (!ipcs.inited) {
        uv_spinlock_init(&ipcs.lock);
        ipcs.r = ipcs.w = 0;
        ipcs.inited = 1;
    }
}

int ipc_queue_send(exo_cap dest, const void *buf, uint64_t len) {
    ipc_init();
    if(!cap_has_rights(dest.rights, EXO_RIGHT_W))
        return -EPERM;
    if(len > sizeof(zipc_msg_t) + sizeof(exo_cap))
        len = sizeof(zipc_msg_t) + sizeof(exo_cap);

    zipc_msg_t m = {0};
    size_t mlen = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);
    memmove(&m, buf, mlen);

    exo_cap fr = {0};
    if(len > sizeof(zipc_msg_t)) {
        memmove(&fr, (const char*)buf + sizeof(zipc_msg_t), sizeof(exo_cap));
        if(!cap_has_rights(fr.rights, EXO_RIGHT_R))
            return -EPERM;
        if(dest.owner)
            fr.owner = dest.owner;
    }

    uv_spinlock_lock(&ipcs.lock);
    while(ipcs.w - ipcs.r == IPC_BUFSZ) {
        uv_spinlock_unlock(&ipcs.lock);
        uv_spinlock_lock(&ipcs.lock);
    }
    ipcs.buf[ipcs.w % IPC_BUFSZ].msg = m;
    ipcs.buf[ipcs.w % IPC_BUFSZ].frame = fr;
    ipcs.w++;
    uv_spinlock_unlock(&ipcs.lock);

    return exo_send(dest, buf, len);
}

int ipc_queue_recv(exo_cap src, void *buf, uint64_t len) {
    if(!cap_has_rights(src.rights, EXO_RIGHT_R))
        return -EPERM;
    ipc_init();
    uv_spinlock_lock(&ipcs.lock);
    while(ipcs.r == ipcs.w) {
        uv_spinlock_unlock(&ipcs.lock);
        char tmp[sizeof(zipc_msg_t) + sizeof(exo_cap)];
        int r = exo_recv(src, tmp, sizeof(tmp));
        if(r > 0) {
            uv_spinlock_lock(&ipcs.lock);
            struct ipc_entry *e = &ipcs.buf[ipcs.w % IPC_BUFSZ];
            memset(e, 0, sizeof(*e));
            size_t cplen = r < sizeof(zipc_msg_t) ? r : sizeof(zipc_msg_t);
            memmove(&e->msg, tmp, cplen);
            if(r > sizeof(zipc_msg_t))
                memmove(&e->frame, tmp + sizeof(zipc_msg_t), r - sizeof(zipc_msg_t));
            ipcs.w++;
        } else {
            uv_spinlock_lock(&ipcs.lock);
        }
    }
    struct ipc_entry e = ipcs.buf[ipcs.r % IPC_BUFSZ];
    ipcs.r++;
    uv_spinlock_unlock(&ipcs.lock);

    size_t total = sizeof(zipc_msg_t);
    if(e.frame.id)
        total += sizeof(exo_cap);
    if(len > sizeof(zipc_msg_t))
        len = len < total ? len : total;
    else
        len = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);

    size_t cplen = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);
    memmove(buf, &e.msg, cplen);
    if(cplen < len)
        memmove((char*)buf + sizeof(zipc_msg_t), &e.frame, len - sizeof(zipc_msg_t));

    return (int)len;
}
