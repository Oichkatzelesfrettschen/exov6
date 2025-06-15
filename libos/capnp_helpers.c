#include "capnp_helpers.h"
#include <string.h>

/**
 * Encode a Cap'n Proto message into a byte buffer.
 *
 * @param msg Message structure to encode.
 * @param len Size of @p msg in bytes.
 * @param buf Destination buffer.
 * @return    Number of bytes written.
 */
size_t capnp_encode(const void *msg, size_t len, unsigned char *buf) {
  memcpy(buf, msg, len);
  return len;
}

/**
 * Decode a Cap'n Proto message from a byte buffer.
 *
 * @param msg Destination message structure.
 * @param len Size of @p msg in bytes.
 * @param buf Source buffer.
 * @return    Number of bytes read.
 */
size_t capnp_decode(void *msg, size_t len, const unsigned char *buf) {
  memcpy(msg, buf, len);
  return len;
}
