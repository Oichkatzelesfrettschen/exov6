/**
 * @file    arbitrate.c
 * @brief   Kernel-internal resource arbitration with policy and logging.
 */

#include "arbitrate.h"
#include "spinlock.h"
#include <string.h>

#ifndef ARB_MAX_ENTRIES
#define ARB_MAX_ENTRIES 64
#endif

#ifndef ARB_LOG_SIZE
#define ARB_LOG_SIZE 32
#endif

struct arb_entry {
  int type;
  int id;
  int owner;
};

static struct {
  struct spinlock lock;
  int inited;
  arb_policy_fn policy;
  struct arb_entry table[ARB_MAX_ENTRIES];
  struct arb_log_entry log[ARB_LOG_SIZE];
  int log_head;
  int log_size;
} state;

static int default_policy(int type, int id, int cur_owner, int requester)
{
  (void)type; (void)id;
  return cur_owner == 0 || cur_owner == requester;
}

/**
 * Initialize arbitration subsystem with default policy.
 */
void arbitrate_init(void)
{
  if (!state.inited) {
    initlock(&state.lock, "arbitrate");
    state.policy = default_policy;
    memset(state.table, 0, sizeof(state.table));
    memset(state.log, 0, sizeof(state.log));
    state.log_head = 0;
    state.log_size = 0;
    state.inited = 1;
  }
}

/**
 * Set arbitration policy.
 * @param fn Optional policy function; NULL selects default.
 */
void arbitrate_set_policy(arb_policy_fn fn)
{
  arbitrate_init();
  acquire(&state.lock);
  state.policy = fn ? fn : default_policy;
  release(&state.lock);
}

static struct arb_entry *find_or_alloc(int type, int id)
{
  for (int i = 0; i < ARB_MAX_ENTRIES; i++) {
    struct arb_entry *e = &state.table[i];
    if (e->owner && e->type == type && e->id == id)
      return e;
  }
  for (int i = 0; i < ARB_MAX_ENTRIES; i++) {
    struct arb_entry *e = &state.table[i];
    if (e->owner == 0) {
      e->type = type;
      e->id = id;
      e->owner = 0;
      return e;
    }
  }
  return 0;
}

/**
 * Request ownership of a resource.
 * @return 0 on grant, -1 on deny.
 */
int arbitrate_request(int type, int resource_id, int owner)
{
  arbitrate_init();
  acquire(&state.lock);
  struct arb_entry *e = find_or_alloc(type, resource_id);
  int granted = 0;
  int cur_owner = e ? e->owner : 0;
  if (e && state.policy(type, resource_id, cur_owner, owner)) {
    e->owner = owner;
    granted = 1;
  }
  int idx = state.log_head;
  state.log[idx].type = type;
  state.log[idx].resource_id = resource_id;
  state.log[idx].owner = owner;
  state.log[idx].granted = granted;
  state.log_head = (state.log_head + 1) % ARB_LOG_SIZE;
  if (state.log_size < ARB_LOG_SIZE) state.log_size++;
  release(&state.lock);
  return granted ? 0 : -1;
}

/**
 * Retrieve recent arbitration decisions.
 * Copies up to max_entries from oldest to newest into out.
 */
size_t arbitration_get_log(struct arb_log_entry *out, size_t max_entries)
{
  arbitrate_init();
  if (!out || max_entries == 0) return 0;
  acquire(&state.lock);
  size_t n = (state.log_size < (int)max_entries) ? (size_t)state.log_size : max_entries;
  for (size_t i = 0; i < n; i++) {
    size_t idx = (state.log_head + ARB_LOG_SIZE - state.log_size + (int)i) % ARB_LOG_SIZE;
    out[i] = state.log[idx];
  }
  release(&state.lock);
  return n;
}

