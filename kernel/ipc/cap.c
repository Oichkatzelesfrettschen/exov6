/**
 * @file cap.c
 * @brief Capability authentication (per-boot keyed MAC, SipHash-2-4 based).
 */

#include <types.h>
#include "exo-userland.h"
#include "defs.h"
#include "timing.h"
#include <string.h>

/* Per-boot secret (initialized in cap_crypto_init). */
static uint64_t sip_k0 = 0, sip_k1 = 0;

/* Rotate-left for 64-bit words. */
static inline uint64_t rotl64(uint64_t x, int b) {
  return (x << b) | (x >> (64 - b));
}

/* One SipRound. */
static inline void sipround(uint64_t st[4]) {
  st[0] += st[1]; st[1] = rotl64(st[1], 13); st[1] ^= st[0]; st[0] = rotl64(st[0], 32);
  st[2] += st[3]; st[3] = rotl64(st[3], 16); st[3] ^= st[2];
  st[0] += st[3]; st[3] = rotl64(st[3], 21); st[3] ^= st[0];
  st[2] += st[1]; st[1] = rotl64(st[1], 17); st[1] ^= st[2]; st[2] = rotl64(st[2], 32);
}

/* SipHash-2-4 with domain separation byte d. */
static uint64_t siphash24_ds(const uint8_t *in, size_t inlen,
                             uint64_t k0, uint64_t k1, uint8_t d)
{
  uint64_t v0 = 0x736f6d6570736575ULL;
  uint64_t v1 = 0x646f72616e646f6dULL;
  uint64_t v2 = 0x6c7967656e657261ULL;
  uint64_t v3 = 0x7465646279746573ULL;
  v0 ^= k0; v1 ^= k1; v2 ^= k0; v3 ^= k1;

  const uint8_t *end = in + inlen - (inlen % 8);
  uint64_t m = 0;
  for (const uint8_t *p = in; p != end; p += 8) {
    m = ((uint64_t)p[0])       | ((uint64_t)p[1] << 8)  |
        ((uint64_t)p[2] << 16) | ((uint64_t)p[3] << 24) |
        ((uint64_t)p[4] << 32) | ((uint64_t)p[5] << 40) |
        ((uint64_t)p[6] << 48) | ((uint64_t)p[7] << 56);
    v3 ^= m;
    uint64_t st[4] = {v0, v1, v2, v3};
    sipround(st); sipround(st);
    v0 = st[0]; v1 = st[1]; v2 = st[2]; v3 = st[3];
    v0 ^= m;
  }

  uint64_t b = ((uint64_t)inlen) << 56 | ((uint64_t)d << 48);
  switch (inlen & 7) {
    case 7: b |= ((uint64_t)end[6]) << 48;  /* fallthrough */
    case 6: b |= ((uint64_t)end[5]) << 40;  /* fallthrough */
    case 5: b |= ((uint64_t)end[4]) << 32;  /* fallthrough */
    case 4: b |= ((uint64_t)end[3]) << 24;  /* fallthrough */
    case 3: b |= ((uint64_t)end[2]) << 16;  /* fallthrough */
    case 2: b |= ((uint64_t)end[1]) << 8;   /* fallthrough */
    case 1: b |= ((uint64_t)end[0]);        /* fallthrough */
    case 0: break;
  }
  v3 ^= b;
  uint64_t st2[4] = {v0, v1, v2, v3};
  sipround(st2); sipround(st2);
  v0 = st2[0]; v1 = st2[1]; v2 = st2[2]; v3 = st2[3];
  v0 ^= b;
  v2 ^= 0xff;
  uint64_t st3[4] = {v0, v1, v2, v3};
  sipround(st3); sipround(st3); sipround(st3); sipround(st3);
  return st3[0] ^ st3[1] ^ st3[2] ^ st3[3];
}

/* Derive 256-bit tag using 4 domain-separated SipHash outputs. */
static void compute_tag(uint id, uint rights, uint owner, hash256_t *out) {
  struct {
    uint id;
    uint rights;
    uint owner;
  } msg = { id, rights, owner };
  const uint8_t *p = (const uint8_t *)&msg;
  out->parts[0] = siphash24_ds(p, sizeof msg, sip_k0, sip_k1, 0x00);
  out->parts[1] = siphash24_ds(p, sizeof msg, sip_k0, sip_k1, 0x01);
  out->parts[2] = siphash24_ds(p, sizeof msg, sip_k0, sip_k1, 0x02);
  out->parts[3] = siphash24_ds(p, sizeof msg, sip_k0, sip_k1, 0x03);
}

/**
 * Initialize per-boot secret used for capability MACs.
 *
 * Seeds two 64-bit SipHash keys by mixing serialized time-stamp counter
 * readings. This is a best-effort entropy source suitable for development
 * builds; production should integrate RDSEED/RDRAND or a hardware RNG.
 */
void cap_crypto_init(void) {
  uint64_t t0 = rdtsc_serialized();
  for (int i = 0; i < 256; ++i) {
    uint64_t ti = rdtsc_serialized();
    t0 ^= rotl64(ti, i & 63) + 0x9e3779b97f4a7c15ULL;
  }
  /* Derive two 64-bit keys via domain-separated SipHash over t0. */
  sip_k0 = siphash24_ds((const uint8_t *)&t0, sizeof t0, 0xa3, 0x94, 0xA0);
  sip_k1 = siphash24_ds((const uint8_t *)&t0, sizeof t0, 0x51, 0xF7, 0xB1);
}

/**
 * Construct a new capability with an authentication tag.
 *
 * @param id      Implementation-defined resource identifier.
 * @param rights  Rights bitmask (EXO_RIGHT_*).
 * @param owner   Owning process/zone identifier.
 * @return        Initialized capability value with MAC.
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
 * Verify a capability's authentication tag using constant-time compare.
 *
 * @param c  Capability to verify.
 * @return   1 if valid, 0 otherwise.
 */
int cap_verify(exo_cap c) {
  hash256_t h;
  compute_tag(c.id, c.rights, c.owner, &h);
  volatile uint64_t diff = 0;
  for (int i = 0; i < 4; ++i) diff |= (h.parts[i] ^ c.auth_tag.parts[i]);
  return diff == 0;
}
