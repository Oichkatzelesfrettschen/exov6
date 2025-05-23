#include "streams.h"
#include "user.h"
#include <string.h>

static void parser_put(queue_t *q, mblk_t *m);
static void encrypt_put(queue_t *q, mblk_t *m);
static void checksum_put(queue_t *q, mblk_t *m);

static struct stream_ops parser_ops = {
    .put = parser_put,
};

static struct stream_ops encrypt_ops = {
    .put = encrypt_put,
};

static struct stream_ops checksum_ops = {
    .put = checksum_put,
};

// simple stub for attach_module when running in user space
void attach_module(queue_t *head, struct stream_ops *mod) {
    mod->next = head->head;
    head->head = mod;
}

static void parser_put(queue_t *q, mblk_t *m) {
    printf(1, "parser: %.*s\n", (int)(m->wp - m->rp), m->rp);
    if (parser_ops.next && parser_ops.next->put)
        parser_ops.next->put(q, m);
}

static void encrypt_put(queue_t *q, mblk_t *m) {
    for (char *p = m->rp; p < m->wp; p++)
        *p ^= 0x20; // trivial transform
    printf(1, "encrypt: %.*s\n", (int)(m->wp - m->rp), m->rp);
    if (encrypt_ops.next && encrypt_ops.next->put)
        encrypt_ops.next->put(q, m);
}

static void checksum_put(queue_t *q, mblk_t *m) {
    unsigned sum = 0;
    for (char *p = m->rp; p < m->wp; p++)
        sum += (unsigned char)*p;
    printf(1, "checksum: %u\n", sum);
    (void)q;
}

int main(void) {
    queue_t q = {0};
    mblk_t msg;
    char data[] = "hello";
    msg.rp = data;
    msg.wp = data + strlen(data);
    attach_module(&q, &checksum_ops);
    attach_module(&q, &encrypt_ops);
    attach_module(&q, &parser_ops);
    if (q.head && q.head->put)
        q.head->put(&q, &msg);
    return 0;
}
