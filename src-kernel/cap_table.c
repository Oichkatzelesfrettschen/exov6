#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "cap.h"
#include <string.h>
#include <stdint.h>

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
            uint id = ((uint)cap_table[i].epoch << 16) | i;
            release(&cap_lock);
            return id;
        }
    }
    release(&cap_lock);
    return -1;
}

int cap_table_lookup(uint id, struct cap_entry *out) {
    uint16_t idx = id & 0xffff;
    uint16_t epoch = id >> 16;
    acquire(&cap_lock);
    if (idx >= CAP_MAX || cap_table[idx].type == CAP_TYPE_NONE ||
        cap_table[idx].epoch != epoch) {
        release(&cap_lock);
        return -1;
    }
    if (out)
        *out = cap_table[idx];
    release(&cap_lock);
    return 0;
}

void cap_table_inc(uint id) {
    uint16_t idx = id & 0xffff;
    uint16_t epoch = id >> 16;
    acquire(&cap_lock);
    if (idx < CAP_MAX && cap_table[idx].type != CAP_TYPE_NONE &&
        cap_table[idx].epoch == epoch)
        cap_table[idx].refcnt++;
    release(&cap_lock);
}

void cap_table_dec(uint id) {
    uint16_t idx = id & 0xffff;
    uint16_t epoch = id >> 16;
    acquire(&cap_lock);
    if (idx < CAP_MAX && cap_table[idx].type != CAP_TYPE_NONE &&
        cap_table[idx].epoch == epoch) {
        if (--cap_table[idx].refcnt == 0)
            cap_table[idx].type = CAP_TYPE_NONE;
    }
    release(&cap_lock);
}

int cap_table_remove(uint id) {
    uint16_t idx = id & 0xffff;
    uint16_t epoch = id >> 16;
    acquire(&cap_lock);
    if (idx >= CAP_MAX || cap_table[idx].type == CAP_TYPE_NONE ||
        cap_table[idx].epoch != epoch) {
        release(&cap_lock);
        return -1;
    }
    cap_table[idx].type = CAP_TYPE_NONE;
    release(&cap_lock);
    return 0;
}

int cap_revoke(uint id) {
    uint16_t idx = id & 0xffff;
    uint16_t epoch = id >> 16;
    acquire(&cap_lock);
    if (idx >= CAP_MAX || cap_table[idx].type == CAP_TYPE_NONE ||
        cap_table[idx].epoch != epoch) {
        release(&cap_lock);
        return -1;
    }
    if (cap_table[idx].epoch == 0xffff) {
        release(&cap_lock);
        return -1;
    }
    cap_table[idx].epoch++;
    cap_table[idx].type = CAP_TYPE_NONE;
    cap_table[idx].refcnt = 0;
    release(&cap_lock);
    return 0;
}
