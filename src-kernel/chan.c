#include "chan.h"
#include "kernel/exo_ipc.h"

// Kernel variant of chan_endpoint_send validating the message size
int chan_endpoint_send(chan_t *c, exo_cap dest, const void *msg, size_t len) {
  if (!c || len != msg_desc_size(c->desc))
    return -1;
  return exo_send(dest, msg, len);
}

// Kernel variant of chan_endpoint_recv validating the message size
int chan_endpoint_recv(chan_t *c, exo_cap src, void *msg, size_t len) {
  if (!c || len != msg_desc_size(c->desc))
    return -1;
  return exo_recv(src, msg, len);
}
