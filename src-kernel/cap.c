#include "types.h"
#include "exo.h"
#include "defs.h"

static uint cap_secret = 0xdeadbeef;

static void
gen_hash(uint id, uint rights, uint owner, hash256_t *out)
{
    for(int i = 0; i < 32; i++)
        out->bytes[i] = (uchar)(cap_secret ^ id ^ rights ^ owner ^ i);
}

exo_cap
cap_new(uint id, uint rights, uint owner)
{
    exo_cap c;
    c.id = id;
    c.rights = rights;
    c.owner = owner;
    gen_hash(id, rights, owner, &c.auth_tag);
    return c;
}

int
cap_verify(exo_cap c)
{
    hash256_t h;
    gen_hash(c.id, c.rights, c.owner, &h);
    return memcmp(h.bytes, c.auth_tag.bytes, sizeof(h.bytes)) == 0;
}
