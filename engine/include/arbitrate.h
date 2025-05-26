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
