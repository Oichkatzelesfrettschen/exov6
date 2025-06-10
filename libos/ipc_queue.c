#include "include/exokernel.h"
#include "exo_ipc.h"
#include "ipc.h"
#include "proc.h"
#include <string.h>
#include <errno.h>
#include "ipc_debug.h"

static void ipc_init(struct mailbox *mb) {
    if(!mb->inited){
        initlock(&mb->lock, "ipcq");
        mb->r = mb->w = 0;
        mb->inited = 1;
    }
}



int ipc_queue_send(exo_cap dest, const void *buf, uint64_t len) {
    struct mailbox *mb = myproc()->mailbox;
    ipc_init(mb);
    IPC_LOG("send attempt dest=%u len=%llu", dest.id, (unsigned long long)len);
    if(!cap_has_rights(dest.rights, EXO_RIGHT_W))
        {
            IPC_LOG("send fail: no write rights");
        return -EPERM;
        }
    if(len > sizeof(zipc_msg_t) + sizeof(exo_cap))
        len = sizeof(zipc_msg_t) + sizeof(exo_cap);

    zipc_msg_t m = {0};
    size_t mlen = len < sizeof(zipc_msg_t) ? len : sizeof(zipc_msg_t);
    memmove(&m, buf, mlen);

    exo_cap fr = {0};
    if(len > sizeof(zipc_msg_t)) {
        memmove(&fr, (const char*)buf + sizeof(zipc_msg_t), sizeof(exo_cap));
        if(!cap_has_rights(fr.rights, EXO_RIGHT_R)) {
            IPC_LOG("send fail: frame lacks read rights");
            return -EPERM;
        }
        if(dest.owner)
            fr.owner = dest.owner;
    }

    acquire(&mb->lock);
    while(mb->w - mb->r == MAILBOX_BUFSZ) {
        IPC_LOG("send waiting: mailbox full");
        release(&mb->lock);
        acquire(&mb->lock);
    }
    mb->buf[mb->w % MAILBOX_BUFSZ].msg = m;
    mb->buf[mb->w % MAILBOX_BUFSZ].frame = fr;
    mb->w++;
    release(&mb->lock);

    IPC_LOG("send complete len=%llu", (unsigned long long)len);

    return exo_send(dest, buf, len);
}

int ipc_queue_recv(exo_cap src, void *buf, uint64_t len) {
    IPC_LOG("recv attempt src=%u", src.id);
    if(!cap_has_rights(src.rights, EXO_RIGHT_R)) {
        IPC_LOG("recv fail: no read rights");
        return -EPERM;
    }
    struct mailbox *mb = myproc()->mailbox;
    ipc_init(mb);
    acquire(&mb->lock);
    while(mb->r == mb->w) {
        IPC_LOG("recv waiting: mailbox empty");
        release(&mb->lock);
        char tmp[sizeof(zipc_msg_t) + sizeof(exo_cap)];
        int r = exo_recv(src, tmp, sizeof(tmp));
        if(r > 0) {
            acquire(&mb->lock);
            struct ipc_entry *e = &mb->buf[mb->w % MAILBOX_BUFSZ];
            memset(e, 0, sizeof(*e));
            size_t cplen = r < sizeof(zipc_msg_t) ? r : sizeof(zipc_msg_t);
            memmove(&e->msg, tmp, cplen);
            if(r > sizeof(zipc_msg_t))
                memmove(&e->frame, tmp + sizeof(zipc_msg_t), r - sizeof(zipc_msg_t));
            mb->w++;
        } else {
            IPC_LOG("recv poll failed");
            acquire(&mb->lock);
        }
    }
    struct ipc_entry e = mb->buf[mb->r % MAILBOX_BUFSZ];
    mb->r++;
    release(&mb->lock);

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

    IPC_LOG("recv complete len=%llu", (unsigned long long)len);

    return (int)len;
}
