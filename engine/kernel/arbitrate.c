/*
 * arbitrate.c - Resource arbitration module
 *
 * This module provides a simple mechanism for arbitrating ownership of
 * resources among multiple requesters, using a configurable policy. It
 * maintains a table of resource entries, each tracking the type, resource ID,
 * and current owner. The arbitration policy determines whether a new requester
 * can take ownership from the current owner.
 *
 * Key Components:
 * ----------------
 * - struct arbitrate_table: Table holding resource arbitration entries and a
 * spinlock.
 * - struct arbitrate_entry: Represents a single resource arbitration entry.
 * - arbitrate_policy_t: Function pointer type for arbitration policy.
 * - default_policy: Default policy that always keeps the current owner.
 * - arbitrate_use_table: Initializes and selects the arbitration table.
 * - arbitrate_init: Initializes the arbitration system with a given policy.
 * - arbitrate_register_policy: Registers a new arbitration policy.
 * - arbitrate_request: Requests ownership of a resource; applies the policy to
 * decide.
 *
 * Thread Safety:
 * --------------
 * All operations on the arbitration table are protected by a spinlock.
 *
 * Usage:
 * ------
 * 1. Optionally register a custom policy with arbitrate_register_policy().
 * 2. Request resource ownership with arbitrate_request().
 * 3. The arbitration system will grant, deny, or transfer ownership based on
 * the policy.
 *
 * Notes:
 * ------
 * - If the spinlock implementation is missing, a minimal dummy version is
 * provided.
 * - The maximum number of arbitration entries is defined by ARB_MAX (default
 * 16).
 * - Logging is performed via cprintf.
 */
#include "arbitrate.h"
#include "spinlock.h"
extern void acquire(struct spinlock *lk);
extern void release(struct spinlock *lk);
#include <stdint.h>
#include <string.h>
#include "spinlock.h"

// #include "defs.h" // Removed because file not found and not required for this
// code

// Forward declarations for required types and functions
#ifndef ARBITRATE_H
#define ARBITRATE_H

#ifndef ARB_MAX
#define ARB_MAX 16
#endif

typedef int (*arbitrate_policy_t)(uint32_t type, uint32_t res, uint32_t cur,
                                  uint32_t new_owner);

uint32_t owner;

/* struct arbitrate_table is defined in arbitrate.h */

#endif // ARBITRATE_H

// Declare cprintf if not already declared
int cprintf(const char *fmt, ...);

#ifndef ARB_MAX
#define ARB_MAX 16
#endif

static struct arbitrate_table default_table;
static int initialized;
static struct arbitrate_table *tbl = &default_table;

static int default_policy(uint32_t type, uint32_t res, uint32_t cur,
                          uint32_t newo) {
  (void)type;
  (void)res;
  (void)cur;
  (void)newo;
  return 0; // keep current owner
}

static arbitrate_policy_t policy = default_policy;

void arbitrate_use_table(struct arbitrate_table *t) {
  if (!t)
    t = &default_table;
  tbl = t;
  initlock(&tbl->lock, "arb");
  memset(tbl->entries, 0, sizeof(tbl->entries));
  initialized = 1;
}

void arbitrate_init(arbitrate_policy_t p) {
  arbitrate_use_table(&default_table);
  if (p)
    policy = p;
}

void arbitrate_register_policy(arbitrate_policy_t p) {
  if (p)
    policy = p;
}

int arbitrate_request(uint32_t type, uint32_t resource_id, uint32_t owner) {
  if (!initialized)
    arbitrate_init(policy);

  acquire(&tbl->lock);
  int free_idx = -1;
  struct arbitrate_entry *match = 0;
  for (int i = 0; i < ARB_MAX; i++) {
    struct arbitrate_entry *e = &tbl->entries[i];
    if (e->owner == 0) {
      if (free_idx < 0)
        free_idx = i;
      continue;
    }
    if (e->type == type && e->resource_id == resource_id) {
      match = e;
      break;
    }
  }

  if (!match) {
    if (free_idx < 0) {
      release(&tbl->lock);
      cprintf("arbitrate: no slot for %u/%u\n", type, resource_id);
      return -1;
    }
    match = &tbl->entries[free_idx];
    match->type = type;
    match->resource_id = resource_id;
    match->owner = owner;
    release(&tbl->lock);
    cprintf("arbitrate: grant %u/%u to %u\n", type, resource_id, owner);
    return 0;
  }

  if (match->owner == owner) {
    release(&tbl->lock);
    return 0;
  }

  int allow = policy ? policy(type, resource_id, match->owner, owner) : 0;
  if (allow) {
    uint32_t old = match->owner;
    match->owner = owner;
    release(&tbl->lock);
    cprintf("arbitrate: replace %u/%u %u -> %u\n", type, resource_id, old,
            owner);
    return 0;
  }

  release(&tbl->lock);
  cprintf("arbitrate: deny %u/%u to %u (owner %u)\n", type, resource_id, owner,
          match->owner);
  return -1;
}
