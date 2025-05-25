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

#include "defs.h"
#include <string.h>

#ifndef ARB_MAX
#define ARB_MAX 16
#endif

static struct arbitrate_table default_table;
static int initialized;
static struct arbitrate_table *tbl = &default_table;

static int default_policy(uint type, uint res, uint cur, uint newo) {
    (void)type; (void)res; (void)cur; (void)newo;
    return 0; // keep current owner
}

static arbitrate_policy_t policy = default_policy;

void
arbitrate_use_table(struct arbitrate_table *t)
{
    if(!t)
        t = &default_table;
    tbl = t;
    initlock(&tbl->lock, "arb");
    memset(tbl->entries, 0, sizeof(tbl->entries));
    initialized = 1;
}

void
arbitrate_init(arbitrate_policy_t p)
{
    arbitrate_use_table(&default_table);
    if(p)
        policy = p;
}

void
arbitrate_register_policy(arbitrate_policy_t p)
{
    if(p)
        policy = p;
}

int
arbitrate_request(uint type, uint resource_id, uint owner)
{
    if(!initialized)
        arbitrate_init(policy);

    acquire(&tbl->lock);
    int free_idx = -1;
    struct arbitrate_entry *match = 0;
    for(int i=0;i<ARB_MAX;i++){
        struct arbitrate_entry *e = &tbl->entries[i];
        if(e->owner == 0){
            if(free_idx < 0)
                free_idx = i;
            continue;
        }
        if(e->type == type && e->resource_id == resource_id){
            match = e;
            break;
        }
    }

    if(!match){
        if(free_idx < 0){
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

    if(match->owner == owner){
        release(&tbl->lock);
        return 0;
    }

    int allow = policy ? policy(type, resource_id, match->owner, owner) : 0;
    if(allow){
        uint old = match->owner;
        match->owner = owner;
        release(&tbl->lock);
        cprintf("arbitrate: replace %u/%u %u -> %u\n", type, resource_id, old, owner);
        return 0;
    }

    release(&tbl->lock);
    cprintf("arbitrate: deny %u/%u to %u (owner %u)\n", type, resource_id, owner, match->owner);
    return -1;
}
