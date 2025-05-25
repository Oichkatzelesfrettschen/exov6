#pragma once
#include "types.h"
#include "caplib.h"

#ifdef __cplusplus
extern "C" {
#endif

// Register the calling process with the rcrs supervisor
int microkernel_register(void);

// Capability helpers
exo_cap mk_cap_alloc_page(void);
int mk_cap_free_page(exo_cap cap);

// Message routing helpers
int mk_route_message(exo_cap dest, const void *buf, size_t len);
int mk_register_endpoint(exo_cap ep);
int mk_unregister_endpoint(exo_cap ep);

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
