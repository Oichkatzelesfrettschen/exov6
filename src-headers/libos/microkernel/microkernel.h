#pragma once
#include "types.h"
#include "caplib.h"
#include "affine_runtime.h"

#ifdef __cplusplus
extern "C" {
#endif

// Register the calling process with the rcrs supervisor
int microkernel_register(void);

// Capability helpers
exo_cap mk_cap_alloc_page(void);
int mk_cap_free_page(exo_cap cap);
int mk_obtain_cap(exo_cap cap, exo_cap *out);
int mk_revoke_cap(exo_cap cap);

// Message routing helpers
int mk_route_message(exo_cap dest, const void *buf, size_t len);
int mk_register_endpoint(exo_cap ep);
int mk_unregister_endpoint(exo_cap ep);

// Lambda capability helpers
lambda_cap_t *mk_lambda_cap_create(lambda_fn fn, void *env, exo_cap cap);
void mk_lambda_cap_destroy(lambda_cap_t *lc);
int mk_lambda_cap_use(lambda_cap_t *lc, int fuel);
int mk_lambda_cap_delegate(lambda_cap_t *lc, uint16_t new_owner);
int mk_lambda_cap_revoke(lambda_cap_t *lc);

// Simple resource accounting structure
typedef struct {
    uint64_t used;
} mk_account_t;

void mk_account_init(mk_account_t *a);
void mk_account_charge(mk_account_t *a, uint64_t amount);
uint64_t mk_account_usage(const mk_account_t *a);

#ifdef __cplusplus
}
#endif
