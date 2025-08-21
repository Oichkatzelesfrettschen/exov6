<<<<<<< HEAD
#include "arbitrate.h"
#include "spinlock.h"
#include <stddef.h>
#include <string.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <unistd.h>
#include <sys/stat.h>
#include <fcntl.h>

#ifndef ARB_MAX_ENTRIES
#define ARB_MAX_ENTRIES 64
#endif

#ifndef ARB_LOG_SIZE
#define ARB_LOG_SIZE 16
#endif

struct arb_entry {
    int type;
    int id;
    int owner;
};

struct arb_state {
    struct arb_entry table[ARB_MAX_ENTRIES];
    struct arb_log_entry log[ARB_LOG_SIZE];
    int log_head;
    int log_size;
};

static struct arb_state *state;
static int state_fd = -1;
static struct spinlock init_lock;
static arb_policy_fn current_policy;

static int default_policy(int type, int id, int cur_owner, int requester){
    (void)type; (void)id;
    return cur_owner == 0 || cur_owner == requester;
}

static void ensure_init(void){
    if(state)
        return;
    acquire(&init_lock);
    if(state){
        release(&init_lock);
        return;
    }
    current_policy = default_policy;
    int oflags = O_RDWR | 0100; /* use standard O_CREAT bit */
    state_fd = open("/tmp/arbitrate_shm", oflags, 0600);
    if(state_fd >= 0){
        ftruncate(state_fd, sizeof(struct arb_state));
        state = mmap(NULL, sizeof(struct arb_state), PROT_READ|PROT_WRITE,
                     MAP_SHARED, state_fd, 0);
        if(state == MAP_FAILED)
            state = NULL;
    }
    if(state)
        memset(state, 0, sizeof(*state));
    release(&init_lock);
}

void arbitrate_init(void){
    initlock(&init_lock, "arbinit");
    ensure_init();
}

void arbitrate_set_policy(arb_policy_fn fn){
    ensure_init();
    acquire(&init_lock);
    current_policy = fn ? fn : default_policy;
    release(&init_lock);
}

static struct arb_entry *find_or_alloc(int type, int id){
    for(int i=0;i<ARB_MAX_ENTRIES;i++){
        struct arb_entry *e = &state->table[i];
        if(e->owner && e->type == type && e->id == id)
            return e;
    }
    for(int i=0;i<ARB_MAX_ENTRIES;i++){
        struct arb_entry *e = &state->table[i];
        if(e->owner == 0){
            e->type = type;
            e->id = id;
            e->owner = 0;
            return e;
        }
    }
    return NULL;
}

int arbitrate_request(int type, int resource_id, int owner){
    ensure_init();
    if(!state)
        return -1;
    flock(state_fd, LOCK_EX);
    struct arb_entry *e = find_or_alloc(type, resource_id);
    int granted = 0;
    int cur_owner = e ? e->owner : 0;
    if(e && current_policy(type, resource_id, cur_owner, owner)){
        e->owner = owner;
        granted = 1;
    }
    int idx = state->log_head;
    state->log[idx].type = type;
    state->log[idx].resource_id = resource_id;
    state->log[idx].owner = owner;
    state->log[idx].granted = granted;
    state->log_head = (state->log_head + 1) % ARB_LOG_SIZE;
    if(state->log_size < ARB_LOG_SIZE)
        state->log_size++;
    flock(state_fd, LOCK_UN);
    return granted ? 0 : -1;
}

size_t arbitration_get_log(struct arb_log_entry *out, size_t max_entries){
    ensure_init();
    if(!state || !out || max_entries==0)
        return 0;
    flock(state_fd, LOCK_EX);
    size_t n = state->log_size < max_entries ? state->log_size : max_entries;
    for(size_t i=0;i<n;i++){
        size_t idx = (state->log_head + ARB_LOG_SIZE - state->log_size + i) % ARB_LOG_SIZE;
        out[i] = state->log[idx];
    }
    flock(state_fd, LOCK_UN);
    return n;
=======
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
>>>>>>> origin/feature/epoch-cache-design-progress
}
