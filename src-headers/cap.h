#pragma once
#include "types.h"
#include <stdint.h>

#define CAP_MAX 1024

enum cap_type {
    CAP_TYPE_NONE    = 0,
    CAP_TYPE_PAGE    = 1,
    CAP_TYPE_IOPORT  = 2,
    CAP_TYPE_IRQ     = 3,
    CAP_TYPE_DMA     = 4,
};

struct cap_entry {
    uint16_t type;
    uint16_t refcnt;
    uint16_t epoch;
    uint32_t resource;
    uint32_t rights;
    uint32_t owner;
};
// The capability table layout is part of the public ABI.  All translation
// units (C and C++) rely on this size and alignment.  Expected size: 20 bytes
// and expected alignment: 4 bytes.
#ifdef __cplusplus
static_assert(sizeof(struct cap_entry) == 20, "ABI mismatch");
#else
_Static_assert(sizeof(struct cap_entry) == 20, "ABI mismatch");
#endif

extern uint32_t global_epoch;

void cap_table_init(void);
int cap_table_alloc(uint16_t type, uint32_t resource, uint32_t rights, uint32_t owner);
int cap_table_lookup(uint32_t id, struct cap_entry *out);
void cap_table_inc(uint32_t id);
void cap_table_dec(uint32_t id);
int cap_table_remove(uint32_t id);
/*
 * Revoke the capability identified by 'id'. The function increments the
 * internal epoch counter encoded in the upper 16 bits of the identifier and
 * marks the entry free. Revocation fails if incrementing would cause the
 * epoch to wrap past 0xffff.
 */
int cap_revoke(uint32_t id);
