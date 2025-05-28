#include "microkernel/microkernel.h"

void mk_account_init(mk_account_t *a) {
    if (a)
        a->used = 0;
}

void mk_account_charge(mk_account_t *a, uint64_t amount) {
    if (a)
        a->used += amount;
}

uint64_t mk_account_usage(const mk_account_t *a) {
    return a ? a->used : 0;
}
