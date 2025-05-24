#pragma once
#include "types.h"

#define CAP_MAX 1024

enum cap_type {
    CAP_TYPE_NONE = 0,
    CAP_TYPE_PAGE = 1,
};

struct cap_entry {
    uint16_t type;
    uint16_t refcnt;
    uint resource;
    uint rights;
    uint owner;
    uint epoch;
};

extern uint global_epoch;

void cap_table_init(void);
int cap_table_alloc(uint16_t type, uint resource, uint rights, uint owner);
int cap_table_lookup(uint16_t id, struct cap_entry *out);
void cap_table_inc(uint16_t id);
void cap_table_dec(uint16_t id);
int cap_table_remove(uint16_t id);
