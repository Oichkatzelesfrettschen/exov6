#pragma once
#include <stddef.h>

struct arb_log_entry {
    int type;
    int resource_id;
    int owner;
    int granted;
};

typedef int (*arb_policy_fn)(int type, int resource_id, int current_owner, int requester);

void arbitrate_init(void);
void arbitrate_set_policy(arb_policy_fn fn);
int arbitrate_request(int type, int resource_id, int owner);
size_t arbitration_get_log(struct arb_log_entry *out, size_t max_entries);

#include "types.h"
#include <spinlock.h>

struct arbitrate_entry {
    uint type;
    uint resource_id;
    uint owner;
};

struct arbitrate_table {
    struct spinlock lock;
    struct arbitrate_entry entries[16];
};

typedef int (*arbitrate_policy_t)(uint type, uint resource_id,
                                   uint current_owner, uint new_owner);

void arbitrate_init(arbitrate_policy_t policy);
void arbitrate_use_table(struct arbitrate_table *t);
void arbitrate_register_policy(arbitrate_policy_t policy);
int arbitrate_request(uint type, uint resource_id, uint owner);
