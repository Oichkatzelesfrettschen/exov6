#include "chan.h"
#include "user.h"
#include "caplib.h"

[[nodiscard]] chan_t *chan_create(const struct msg_type_desc *desc) {
  chan_t *c = malloc(sizeof(chan_t));
  if (c) {
    c->desc = desc;
    c->msg_size = msg_desc_size(desc);
  }
  return c;
}

void chan_destroy(chan_t *c) { free(c); }

[[nodiscard]] exo_ipc_status chan_endpoint_send(chan_t *c, exo_cap dest,
                                                const void *msg, size_t len) {
  if (len != c->msg_size) {
    printf(2, "chan_endpoint_send: size %d != %d\n", (int)len,
           (int)c->msg_size);
    return -1;
  }
  return cap_send(dest, msg, c->msg_size);
}

[[nodiscard]] exo_ipc_status chan_endpoint_recv(chan_t *c, exo_cap src, void *msg,
                                                size_t len) {
  if (len != c->msg_size) {
    printf(2, "chan_endpoint_recv: size %d != %d\n", (int)len,
           (int)c->msg_size);
    return -1;
  }
  return cap_recv(src, msg, c->msg_size);
}
