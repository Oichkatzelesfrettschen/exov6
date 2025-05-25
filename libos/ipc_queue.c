#include "include/exokernel.h"
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

static void mbox_init(struct exo_mailbox *mb) {
    uv_spinlock_init(&mb->lock);
    mb->r = mb->w = 0;
}

int ipc_queue_send(struct exo_mailbox *mb, exo_cap dest, const void *buf,
                   uint64_t len) {
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

    if(mb->r == 0 && mb->w == 0)
        mbox_init(mb);
    uv_spinlock_lock(&mb->lock);
    while(mb->w - mb->r == IPC_BUFSZ) {
        uv_spinlock_unlock(&mb->lock);
        uv_spinlock_lock(&mb->lock);
    }
    mb->buf[mb->w % IPC_BUFSZ].msg = m;
    mb->buf[mb->w % IPC_BUFSZ].frame = fr;
    mb->w++;
    uv_spinlock_unlock(&mb->lock);

    return exo_send(dest, buf, len);
}

int ipc_queue_recv(struct exo_mailbox *mb, exo_cap src, void *buf, uint64_t len) {
    if(!cap_has_rights(src.rights, EXO_RIGHT_R))
        return -EPERM;
    if(mb->r == 0 && mb->w == 0)
        mbox_init(mb);
    uv_spinlock_lock(&mb->lock);
    while(mb->r == mb->w) {
        uv_spinlock_unlock(&mb->lock);
        char tmp[sizeof(zipc_msg_t) + sizeof(exo_cap)];
        int r = exo_recv(src, tmp, sizeof(tmp));
        if(r > 0) {
            uv_spinlock_lock(&mb->lock);
            struct ipc_entry *e = &mb->buf[mb->w % IPC_BUFSZ];
            memset(e, 0, sizeof(*e));
            size_t cplen = r < sizeof(zipc_msg_t) ? r : sizeof(zipc_msg_t);
            memmove(&e->msg, tmp, cplen);
            if(r > sizeof(zipc_msg_t))
                memmove(&e->frame, tmp + sizeof(zipc_msg_t), r - sizeof(zipc_msg_t));
            mb->w++;
        } else {
            uv_spinlock_lock(&mb->lock);
        }
    }
    struct ipc_entry e = mb->buf[mb->r % IPC_BUFSZ];
    mb->r++;
    uv_spinlock_unlock(&mb->lock);

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
