#include <stdio.h>
#include <stdint.h>
#include <string.h>

/*
 * Capability State Machine - C model aligned with Capability.tla
 * --------------------------------------------------------------
 * This simple C translation mirrors the state transitions of the
 * TLA+ specification located in Capability.tla. The model keeps
 * track of a small set of capability IDs and their owners along
 * with the currently active capability.
 */

#define MAX_CAPS 64
#define NULL_CAP 0u

typedef struct {
    uint32_t owner[MAX_CAPS];
    uint8_t in_use[MAX_CAPS];
    uint32_t active;
} CapabilityModel;

void model_init(CapabilityModel *m)
{
    memset(m, 0, sizeof(*m));
    m->active = NULL_CAP;
}

/* Create(c,u) */
int model_create(CapabilityModel *m, uint32_t c, uint32_t u)
{
    if (c >= MAX_CAPS || m->in_use[c])
        return -1;
    m->in_use[c] = 1;
    m->owner[c] = u;
    return 0;
}

/* Revoke(c,u) */
int model_revoke(CapabilityModel *m, uint32_t c, uint32_t u)
{
    if (c >= MAX_CAPS || !m->in_use[c] || m->owner[c] != u)
        return -1;
    m->in_use[c] = 0;
    if (m->active == c)
        m->active = NULL_CAP;
    return 0;
}

/* YieldTo(src,dst,u) */
int model_yield_to(CapabilityModel *m, uint32_t src, uint32_t dst, uint32_t u)
{
    if (src >= MAX_CAPS || dst >= MAX_CAPS)
        return -1;
    if (!m->in_use[src] || !m->in_use[dst])
        return -1;
    if (m->owner[src] != u || m->active != src)
        return -1;
    m->active = dst;
    return 0;
}

/* ActiveInv */
int model_active_inv(const CapabilityModel *m)
{
    if (m->active == NULL_CAP)
        return 1;
    if (m->active < MAX_CAPS && m->in_use[m->active])
        return 1;
    return 0;
}

#ifdef CAPABILITY_MODEL_DEMO
int main(void)
{
    CapabilityModel m;
    model_init(&m);

    model_create(&m, 1, 42);
    model_create(&m, 2, 42);
    m.active = 1;
    model_yield_to(&m, 1, 2, 42);
    printf("Active capability: %u\n", m.active);
    printf("Invariant holds: %s\n", model_active_inv(&m) ? "yes" : "no");
    return 0;
}
#endif
