#include "chan.h"
#include "user.h"
#include "caplib.h"

/**
 * @brief Allocate a new channel.
 *
 * @param desc Message descriptor providing encode/decode helpers.
 * @return Newly allocated channel or NULL on allocation failure.
 */
EXO_NODISCARD chan_t *chan_create(const struct msg_type_desc *desc) {
  chan_t *c = malloc(sizeof(*c));
  if (c) {
    c->desc = desc;
    c->msg_size = msg_desc_size(desc);
  }
  return c;
}

/** Destroy a channel created with chan_create. */
void chan_destroy(chan_t *c) { free(c); }

/**
 * @brief Send a message through an endpoint.
 *
 * @param c    Channel descriptor.
 * @param dest Capability representing the destination endpoint.
 * @param msg  Buffer containing the message.
 * @param len  Length of the message in bytes.
 * @return 0 on success, -1 on size mismatch or underlying send failure.
 */
EXO_NODISCARD int chan_endpoint_send(chan_t *c, exo_cap dest, const void *msg,
                                     size_t len) {
  if (len > c->msg_size) {
    printf(2, "chan_endpoint_send: size %d > %d\n", (int)len, (int)c->msg_size);
    return -1;
  }
  return cap_send(dest, msg, len);
}

/**
 * @brief Receive a message from an endpoint.
 *
 * @param c    Channel descriptor.
 * @param src  Capability representing the source endpoint.
 * @param msg  Buffer to store the message.
 * @param len  Maximum number of bytes to receive.
 * @return 0 on success, -1 on size mismatch or underlying receive failure.
 */
EXO_NODISCARD int chan_endpoint_recv(chan_t *c, exo_cap src, void *msg,
                                     size_t len) {
  if (len > c->msg_size) {
    printf(2, "chan_endpoint_recv: size %d > %d\n", (int)len, (int)c->msg_size);
    return -1;
  }
  return cap_recv(src, msg, len);
}
