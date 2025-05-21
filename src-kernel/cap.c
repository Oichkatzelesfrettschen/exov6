#include "types.h"
#include "exo.h"
#include "defs.h"
#include <string.h>

  
/* Secret key used for capability HMAC */
static const uint8_t cap_secret[32] = {
    0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef,
    0xfe,0xdc,0xba,0x98,0x76,0x54,0x32,0x10,
    0x55,0xaa,0x55,0xaa,0x00,0x11,0x22,0x33,
    0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb
};

/* 64-bit FNV-1a hash used by the HMAC implementation */
static uint64
fnv64(const uint8_t *data, size_t len, uint64 seed)
{
    const uint64 prime = 1099511628211ULL;
    uint64 h = seed;
    for(size_t i = 0; i < len; i++) {
        h ^= data[i];
        h *= prime;
    }
    return h;
}

/* Hash data into four 64-bit words */
static void
hash256(const uint8_t *data, size_t len, hash256_t *out)
{
    const uint64 basis = 14695981039346656037ULL;
    for(int i = 0; i < 4; i++)
        out->parts[i] = fnv64(data, len, basis + i);
}

/* Derive the authentication tag for a capability. */
static void
compute_tag(uint id, uint rights, uint owner, hash256_t *out)
{
    struct { uint id; uint rights; uint owner; } tmp = { id, rights, owner };
    uint8_t buf[sizeof(cap_secret) + sizeof(tmp)];

    memmove(buf, cap_secret, sizeof(cap_secret));
    memmove(buf + sizeof(cap_secret), &tmp, sizeof(tmp));
    hash256(buf, sizeof(buf), out);
}

exo_cap
cap_new(uint id, uint rights, uint owner)
{
    exo_cap c;
    c.id = id;
    c.rights = rights;
    c.owner = owner;
    compute_tag(id, rights, owner, &c.auth_tag);
    return c;
}

int
cap_verify(exo_cap c)
{
    hash256_t h;
    compute_tag(c.id, c.rights, c.owner, &h);
    return memcmp(h.bytes, c.auth_tag.bytes, sizeof(h.bytes)) == 0;
}

