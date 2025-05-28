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
}
