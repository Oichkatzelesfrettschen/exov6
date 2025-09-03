/**
 * @file    cap_table.c
 * @brief   Minimal capability table (index+epoch ids, free-list management).
 */

#include <types.h>
#include "defs.h"
#include "cap.h"
#include <string.h>

uint32_t global_epoch = 1;
int cap_table_ready = 0;

static struct spinlock cap_lock;
static struct cap_entry cap_table[CAP_MAX];
static uint16_t free_head;           /* 0 means empty */
static uint16_t next_free[CAP_MAX];  /* next index for free list */

static inline uint16_t id_index(uint32_t id) { return (uint16_t)(id & 0xFFFFu); }
static inline uint16_t id_epoch(uint32_t id) { return (uint16_t)((id >> 16) & 0xFFFFu); }
static inline uint32_t make_id(uint16_t idx, uint16_t ep) { return ((uint32_t)ep << 16) | idx; }

/** Initialize capability table and free list. */
void cap_table_init(void)
{
  initlock(&cap_lock, "cap_table");
  memset(cap_table, 0, sizeof cap_table);
  memset(next_free, 0, sizeof next_free);
  global_epoch = 1;
  free_head = (CAP_MAX > 1) ? 1 : 0;
  for (uint16_t i = 1; i + 1 < CAP_MAX; ++i) next_free[i] = i + 1;
  if (CAP_MAX > 1) next_free[CAP_MAX - 1] = 0;
  cap_table_ready = 1;
}

/** Allocate an entry and return encoded id (negative on failure). */
int cap_table_alloc(uint16_t type, uint32_t resource, uint32_t rights, uint32_t owner)
{
  if (!cap_table_ready || type == CAP_TYPE_NONE) return -1;
  acquire(&cap_lock);
  uint16_t idx = free_head;
  if (idx == 0) { release(&cap_lock); return -1; }
  free_head = next_free[idx];
  struct cap_entry *e = &cap_table[idx];
  e->type = type;
  e->refcnt = 1;
  e->epoch = (uint16_t)global_epoch;
  e->resource = resource;
  e->rights = rights;
  e->owner = owner;
  int id = (int)make_id(idx, e->epoch);
  release(&cap_lock);
  return id;
}

/** Look up an entry by id. */
int cap_table_lookup(cap_id_t id, struct cap_entry *out)
{
  if (!cap_table_ready || id == 0 || !out) return -1;
  uint16_t idx = id_index((uint32_t)id);
  uint16_t ep = id_epoch((uint32_t)id);
  if (idx == 0 || idx >= CAP_MAX) return -1;
  acquire(&cap_lock);
  struct cap_entry e = cap_table[idx];
  int ok = (e.type != CAP_TYPE_NONE) && (e.epoch == ep);
  release(&cap_lock);
  if (!ok) return -1;
  *out = e;
  return 0;
}

/** Increment reference count if valid. */
void cap_table_inc(cap_id_t id)
{
  if (!cap_table_ready || id == 0) return;
  uint16_t idx = id_index((uint32_t)id);
  uint16_t ep = id_epoch((uint32_t)id);
  if (idx == 0 || idx >= CAP_MAX) return;
  acquire(&cap_lock);
  struct cap_entry *e = &cap_table[idx];
  if (e->type != CAP_TYPE_NONE && e->epoch == ep && e->refcnt != 0xFFFF) e->refcnt++;
  release(&cap_lock);
}

/** Decrement reference count and free on zero. */
void cap_table_dec(cap_id_t id)
{
  if (!cap_table_ready || id == 0) return;
  uint16_t idx = id_index((uint32_t)id);
  uint16_t ep = id_epoch((uint32_t)id);
  if (idx == 0 || idx >= CAP_MAX) return;
  acquire(&cap_lock);
  struct cap_entry *e = &cap_table[idx];
  if (e->type != CAP_TYPE_NONE && e->epoch == ep && e->refcnt > 0) {
    if (--e->refcnt == 0) {
      e->type = CAP_TYPE_NONE;
      e->resource = 0; e->rights = 0; e->owner = 0;
      next_free[idx] = free_head; free_head = idx;
    }
  }
  release(&cap_lock);
}

/** Remove entry, regardless of refcount. */
int cap_table_remove(cap_id_t id)
{
  if (!cap_table_ready || id == 0) return -1;
  uint16_t idx = id_index((uint32_t)id);
  uint16_t ep = id_epoch((uint32_t)id);
  if (idx == 0 || idx >= CAP_MAX) return -1;
  acquire(&cap_lock);
  struct cap_entry *e = &cap_table[idx];
  if (e->type == CAP_TYPE_NONE || e->epoch != ep) { release(&cap_lock); return -1; }
  e->type = CAP_TYPE_NONE; e->refcnt = 0; e->resource = 0; e->rights = 0; e->owner = 0;
  next_free[idx] = free_head; free_head = idx;
  release(&cap_lock);
  return 0;
}

/** Revoke: bump epoch and free slot. */
int cap_revoke(cap_id_t id)
{
  if (!cap_table_ready || id == 0) return -1;
  uint16_t idx = id_index((uint32_t)id);
  uint16_t ep = id_epoch((uint32_t)id);
  if (idx == 0 || idx >= CAP_MAX) return -1;
  acquire(&cap_lock);
  struct cap_entry *e = &cap_table[idx];
  if (e->type == CAP_TYPE_NONE || e->epoch != ep) { release(&cap_lock); return -1; }
  if (e->epoch == 0xFFFFu) { release(&cap_lock); return -2; }
  e->epoch++;
  e->type = CAP_TYPE_NONE; e->refcnt = 0; e->resource = 0; e->rights = 0; e->owner = 0;
  if (global_epoch <= e->epoch) global_epoch = (uint32_t)e->epoch + 1u;
  next_free[idx] = free_head; free_head = idx;
  release(&cap_lock);
  return 0;
}

