#include "../include/exokernel.h"
#include "affine_runtime.h"

lambda_cap_t *mk_lambda_cap_create(lambda_fn fn, void *env, exo_cap cap) {
    return lambda_cap_create(fn, env, cap);
}

void mk_lambda_cap_destroy(lambda_cap_t *lc) { lambda_cap_destroy(lc); }

int mk_lambda_cap_use(lambda_cap_t *lc, int fuel) {
    return lambda_cap_use(lc, fuel);
}

int mk_lambda_cap_delegate(lambda_cap_t *lc, uint16_t new_owner) {
    return lambda_cap_delegate(lc, new_owner);
}

int mk_lambda_cap_revoke(lambda_cap_t *lc) { return lambda_cap_revoke(lc); }
