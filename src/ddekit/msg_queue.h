#ifndef DDEKIT_SRC_MSG_QUEUE_H
#define DDEKIT_SRC_MSG_QUEUE_H

#include "ddekit.h"
#include "thread.h"
#include <minix/ipc.h>

struct ddekit_minix_msg_q;

/** Enqueue a Minix message for later delivery. */
void ddekit_minix_queue_msg(message *m, int ipc_status);

/** Receive the next message from the queue. */
void ddekit_minix_rcv(struct ddekit_minix_msg_q *mq, message *m,
                      int *ipc_status);

/** Create a new message queue for a given source/target pair. */
struct ddekit_minix_msg_q *ddekit_minix_create_msg_q(unsigned from,
                                                     unsigned to);

/** Destroy a previously created message queue. */
void ddekit_minix_destroy_msg_q(struct ddekit_minix_msg_q *mq);

#endif /* DDEKIT_SRC_MSG_QUEUE_H */
