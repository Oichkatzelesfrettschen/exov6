#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

typedef unsigned int uint;
typedef unsigned long uint64;

typedef struct hash256 { uint64 parts[4]; } hash256_t;
typedef struct exo_cap { uint pa; uint id; uint rights; uint owner; hash256_t auth_tag; } exo_cap;

static const uint8_t cap_secret[32] = {
    0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef,
    0xfe,0xdc,0xba,0x98,0x76,0x54,0x32,0x10,
    0x55,0xaa,0x55,0xaa,0x00,0x11,0x22,0x33,
    0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb
};

static uint64 fnv64(const uint8_t *data, size_t len, uint64 seed) {
    const uint64 prime = 1099511628211ULL;
    uint64 h = seed;
    for(size_t i=0;i<len;i++) {
        h ^= data[i];
        h *= prime;
    }
    return h;
}

static void hash256(const uint8_t *data, size_t len, hash256_t *out) {
    const uint64 basis = 14695981039346656037ULL;
    for(int i=0;i<4;i++)
        out->parts[i] = fnv64(data, len, basis + i);
}

static void compute_tag(uint id, uint rights, uint owner, hash256_t *out) {
    struct { uint id; uint rights; uint owner; } tmp = { id, rights, owner };
    uint8_t buf[sizeof(cap_secret) + sizeof(tmp)];
    memmove(buf, cap_secret, sizeof(cap_secret));
    memmove(buf + sizeof(cap_secret), &tmp, sizeof(tmp));
    hash256(buf, sizeof(buf), out);
}

static exo_cap cap_new(uint id, uint rights, uint owner) {
    exo_cap c;
    c.pa = 0;
    c.id = id;
    c.rights = rights;
    c.owner = owner;
    compute_tag(id, rights, owner, &c.auth_tag);
    return c;
}

static int cap_verify(exo_cap c) {
    hash256_t h;
    compute_tag(c.id, c.rights, c.owner, &h);
    return memcmp(h.parts, c.auth_tag.parts, sizeof(h.parts)) == 0;
}

static int exo_yield_to(exo_cap target) {
    if (target.pa == 0)
        return -1;
    if (!cap_verify(target))
        return -1;
    return 0;
}

int main(void) {
    const int iters = 100000;
    exo_cap c = cap_new(1,2,3);
    c.pa = 1; // valid address
    struct timespec s,e;
    clock_gettime(CLOCK_MONOTONIC, &s);
    for(int i=0;i<iters;i++)
        exo_yield_to(c);
    clock_gettime(CLOCK_MONOTONIC, &e);
    long long ns = (e.tv_sec - s.tv_sec)*1000000000LL + (e.tv_nsec - s.tv_nsec);
    printf("exo_yield_to: %.2f ns\n", (double)ns/iters);
    return 0;
}
