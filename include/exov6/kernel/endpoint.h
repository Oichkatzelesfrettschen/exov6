#pragma once
#include "ipc.h"
#include "spinlock.h"

struct endpoint {
  struct spinlock lock;
  zipc_msg_t *q;
  uint32_t size;
  uint32_t r, w;
  int inited;
  const struct msg_type_desc *desc;
};

void endpoint_init(struct endpoint *ep);
void endpoint_config(struct endpoint *ep, zipc_msg_t *buf, uint32_t size,
                     const struct msg_type_desc *desc);
void endpoint_send(struct endpoint *ep, zipc_msg_t *m);
EXO_NODISCARD int endpoint_recv(struct endpoint *ep, zipc_msg_t *m);
