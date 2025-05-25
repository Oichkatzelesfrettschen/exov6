#include <stdio.h>
#include <stdint.h>
#include "src-headers/exo.h"
#include <string.h>

static const uint8_t cap_secret[32] = {
    0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef,
    0xfe,0xdc,0xba,0x98,0x76,0x54,0x32,0x10,
    0x55,0xaa,0x55,0xaa,0x00,0x11,0x22,0x33,
    0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb
};

static uint64_t fnv64(const uint8_t *data, size_t len, uint64_t seed)
{
    const uint64_t prime = 1099511628211ULL;
    uint64_t h = seed;
    for(size_t i = 0; i < len; i++){
        h ^= data[i];
        h *= prime;
    }
    return h;
}

static void hash256(const uint8_t *data, size_t len, hash256_t *out)
{
    const uint64_t basis = 14695981039346656037ULL;
    for(int i = 0; i < 4; i++)
        out->parts[i] = fnv64(data, len, basis + i);
}

static void compute_tag(uint id, uint rights, uint owner, hash256_t *out)
{
    struct { uint id; uint rights; uint owner; } tmp = { id, rights, owner };
    uint8_t buf[sizeof(cap_secret) + sizeof(tmp)];
    memmove(buf, cap_secret, sizeof(cap_secret));
    memmove(buf + sizeof(cap_secret), &tmp, sizeof(tmp));
    hash256(buf, sizeof(buf), out);
}

static exo_cap cap_new_local(uint id, uint rights, uint owner)
{
    exo_cap c;
    c.id = id;
    c.rights = rights;
    c.owner = owner;
    compute_tag(id, rights, owner, &c.auth_tag);
    return c;
}

static int cap_verify_local(exo_cap c)
{
    hash256_t h;
    compute_tag(c.id, c.rights, c.owner, &h);
    return memcmp(h.parts, c.auth_tag.parts, sizeof(h.parts)) == 0;
}

static inline uint64_t rdtsc(void)
{
    unsigned hi, lo;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

int main(void)
{
    exo_cap c = cap_new_local(1, 1, 1);
    const int ITER = 1000000;
    uint64_t start = rdtsc();
    for (int i = 0; i < ITER; i++)
        cap_verify_local(c);
    uint64_t end = rdtsc();
    printf("cap_verify: %lu cycles\n", (end - start) / ITER);
    return 0;
}
