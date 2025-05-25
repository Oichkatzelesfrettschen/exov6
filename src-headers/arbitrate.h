#pragma once
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
