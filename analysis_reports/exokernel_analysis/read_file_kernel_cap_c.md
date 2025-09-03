# Analysis Report: `read_file` for `kernel/cap.c`

## Tool Call:
```
default_api.read_file(absolute_path = "/Users/eirikr/Documents/GitHub/exov6/kernel/cap.c")
```

## Output:
```c
#include "types.h"
#include "exo.h"
#include "defs.h"
#include <string.h>

/** Secret key used for capability HMAC. */
static const uint8_t cap_secret[32] = {
    0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0xfe, 0xdc, 0xba,
    0x98, 0x76, 0x54, 0x32, 0x10, 0x55, 0xaa, 0x55, 0xaa, 0x00, 0x11,
    0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb};

/**
 * Compute a 64-bit FNV-1a hash over a buffer.
 *
 * @param data  Input data to hash.
 * @param len   Length of @p data in bytes.
 * @param seed  Initial hash seed.
 * @return      Hash value.
 */
static uint64 fnv64(const uint8_t *data, size_t len, uint64 seed) {
  const uint64 prime = 1099511628211ULL;
  uint64 h = seed;
  for (size_t i = 0; i < len; i++) {
    h ^= data[i];
    h *= prime;
  }
  return h;
}

/**
 * Hash data into four 64-bit words using FNV-1a.
 *
 * @param data Input buffer.
 * @param len  Length of @p data in bytes.
 * @param out  Destination hash.
 */
static void hash256(const uint8_t *data, size_t len, hash256_t *out) {
  const uint64 basis = 14695981039346656037ULL;
  for (int i = 0; i < 4; i++)
    out->parts[i] = fnv64(data, len, basis + i);
}

/**
 * Derive the authentication tag for a capability.
 *
 * @param id      Capability identifier.
 * @param rights  Access rights for the capability.
 * @param owner   Owner identifier.
 * @param out     Computed authentication tag.
 */
static void compute_tag(uint id, uint rights, uint owner, hash256_t *out) {
  struct {
    uint id;
    uint rights;
    uint owner;
  } tmp = {id, rights, owner};
  uint8_t buf[sizeof(cap_secret) + sizeof(tmp)];

  memmove(buf, cap_secret, sizeof(cap_secret));
  memmove(buf + sizeof(cap_secret), &tmp, sizeof(tmp));
  hash256(buf, sizeof(buf), out);
}

/**
 * Construct a new capability with an authentication tag.
 *
 * @param id      Capability identifier.
 * @param rights  Access rights.
 * @param owner   Owner identifier.
 * @return        Initialized capability.
 */
exo_cap cap_new(uint id, uint rights, uint owner) {
  exo_cap c;
  c.id = id;
  c.rights = rights;
  c.owner = owner;
  compute_tag(id, rights, owner, &c.auth_tag);
  return c;
}

/**
 * Verify a capability's authentication tag.
 *
 * @param c  Capability to verify.
 * @return   Non-zero if valid, zero otherwise.
 */
int cap_verify(exo_cap c) {
  hash256_t h;
  compute_tag(c.id, c.rights, c.owner, &h);
  return memcmp(h.parts, c.auth_tag.parts, sizeof(h.parts)) == 0;
}
```