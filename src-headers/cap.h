#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include "types.h"
#include <stdint.h>

#define CAP_MAX 1024

enum cap_type {
  CAP_TYPE_NONE = 0,
  CAP_TYPE_PAGE = 1,
  CAP_TYPE_IOPORT = 2,
  CAP_TYPE_IRQ = 3,
  CAP_TYPE_DMA = 4,
};

struct cap_entry {
  uint16_t type;
  uint16_t refcnt;
  uint16_t epoch;
  uint resource;
  uint rights;
  uint owner;
};

extern uint global_epoch;

void cap_table_init(void);
int cap_table_alloc(uint16_t type, uint resource, uint rights, uint owner);
int cap_table_lookup(uint id, struct cap_entry *out);
void cap_table_inc(uint id);
void cap_table_dec(uint id);
int cap_table_remove(uint id);
/*
 * Revoke the capability identified by 'id'. The function increments the
 * internal epoch counter encoded in the upper 16 bits of the identifier and
 * marks the entry free. Revocation fails if incrementing would cause the
 * epoch to wrap past 0xffff.
 */
int cap_revoke(uint id);
#ifdef __cplusplus
}
#endif
