#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "cap.h"
#include <string.h>

static struct spinlock cap_lock;
static struct cap_entry cap_table[CAP_MAX];
uint global_epoch;

void cap_table_init(void) {
    initlock(&cap_lock, "captbl");
    memset(cap_table, 0, sizeof(cap_table));
    global_epoch = 0;
}

int cap_table_alloc(uint16_t type, uint resource, uint rights, uint owner) {
    acquire(&cap_lock);
    for (int i = 1; i < CAP_MAX; i++) {
        if (cap_table[i].type == CAP_TYPE_NONE) {
            cap_table[i].type = type;
            cap_table[i].resource = resource;
            cap_table[i].rights = rights;
            cap_table[i].owner = owner;
            cap_table[i].refcnt = 1;
            cap_table[i].epoch = global_epoch;
            release(&cap_lock);
            return i;
        }
    }
    release(&cap_lock);
    return -1;
}

int cap_table_lookup(uint16_t id, struct cap_entry *out) {
    acquire(&cap_lock);
    if (id >= CAP_MAX || cap_table[id].type == CAP_TYPE_NONE) {
        release(&cap_lock);
        return -1;
    }
    if (out)
        *out = cap_table[id];
    release(&cap_lock);
    return 0;
}

void cap_table_inc(uint16_t id) {
    acquire(&cap_lock);
    if (id < CAP_MAX && cap_table[id].type != CAP_TYPE_NONE &&
        cap_table[id].epoch == global_epoch)
        cap_table[id].refcnt++;
    release(&cap_lock);
}

void cap_table_dec(uint16_t id) {
    acquire(&cap_lock);
    if (id < CAP_MAX && cap_table[id].type != CAP_TYPE_NONE &&
        cap_table[id].epoch == global_epoch) {
        if (--cap_table[id].refcnt == 0)
            cap_table[id].type = CAP_TYPE_NONE;
    }
    release(&cap_lock);
}

int cap_table_remove(uint16_t id) {
    acquire(&cap_lock);
    if (id >= CAP_MAX || cap_table[id].type == CAP_TYPE_NONE) {
        release(&cap_lock);
        return -1;
    }
    cap_table[id].type = CAP_TYPE_NONE;
    release(&cap_lock);
    return 0;
}
