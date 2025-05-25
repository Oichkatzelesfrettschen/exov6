#include "arbitrate.h"
#include "spinlock.h"
#include "defs.h"
#include <string.h>

#ifndef ARB_MAX
#define ARB_MAX 16
#endif

static struct arbitrate_table default_table;
static int initialized;
static struct arbitrate_table *tbl = &default_table;

static int default_policy(uint32_t type, uint32_t res, uint32_t cur, uint32_t newo) {
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
arbitrate_request(uint32_t type, uint32_t resource_id, uint32_t owner)
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
        uint32_t old = match->owner;
        match->owner = owner;
        release(&tbl->lock);
        cprintf("arbitrate: replace %u/%u %u -> %u\n", type, resource_id, old, owner);
        return 0;
    }

    release(&tbl->lock);
    cprintf("arbitrate: deny %u/%u to %u (owner %u)\n", type, resource_id, owner, match->owner);
    return -1;
}
