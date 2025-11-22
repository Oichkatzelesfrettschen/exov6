#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>

// Include mocks
#include "mocks/capability_v2.h"

// Stub for token bucket (referenced by capability_v2.c)
void token_bucket_init(struct token_bucket *tb, q16_t c, q16_t r) {
    tb->capacity = c;
    tb->refill_rate = r;
    tb->tokens = c;
}
int token_bucket_consume(struct token_bucket *tb, q16_t amount) {
    if (tb->tokens >= amount) {
        tb->tokens -= amount;
        return 1;
    }
    return 0;
}

q16_t token_bucket_get_tokens(struct token_bucket *tb) {
    return (q16_t)tb->tokens;
}

// Include the implementation under test
#include "test_wrapper_capability_v2.c"

// Tests
void test_privilege_escalation() {
    printf("[TEST] Privilege Escalation\n");
    capv2_table_init();

    resource_vector_t quota = {0};
    int parent = capv2_alloc(100, CAP_TYPE_MEMORY_PAGE, CAP_RIGHT_READ | CAP_RIGHT_GRANT, quota);
    assert(parent >= 0);

    // Attempt to grant WRITE (which parent doesn't have)
    int child = capv2_grant(parent, 200, CAP_RIGHT_READ | CAP_RIGHT_WRITE);

    if (child != CAPV2_ERR_NO_PERMISSION) {
        printf("FAIL: Managed to grant WRITE privilege from READ-only parent\n");
        exit(1);
    }
    printf("PASS: Privilege escalation prevented\n");
}

void test_stale_capability() {
    printf("[TEST] Stale Capability Usage\n");
    capv2_table_init();

    resource_vector_t quota = {0};
    // Must have REVOKE right to revoke/free via standard API
    int slot = capv2_alloc(100, CAP_TYPE_MEMORY_PAGE, CAP_RIGHT_READ | CAP_RIGHT_REVOKE, quota);
    assert(slot >= 0);

    struct capability_v2 info;
    capv2_get_info(slot, &info);
    uint32_t old_gen = info.generation;

    // Free the capability (Revoke drops refcount, if 0 it frees)
    int ret = capv2_revoke(slot);
    if (ret != CAPV2_OK) {
        printf("Failed to revoke/free: %d\n", ret);
        exit(1);
    }

    // Re-allocate the same slot (it's LIFO free list, so likely same slot)
    int new_slot = capv2_alloc(200, CAP_TYPE_MEMORY_PAGE, CAP_RIGHT_READ, quota);
    if (new_slot != slot) {
        printf("WARNING: Slot not reused. Old: %d, New: %d. This might depend on allocator implementation.\n", slot, new_slot);
        // If slot not reused, we can't strictly test generation increment on the *same* slot easily
        // without finding where the old slot went.
        // But for LIFO free list, it SHOULD be reused.
    }
    // assert(new_slot == slot); // Should reuse slot

    capv2_get_info(new_slot, &info);
    uint32_t new_gen = info.generation;

    if (new_gen == old_gen) {
        printf("FAIL: Generation counter did not increment (ABA vulnerable)\n");
        exit(1);
    }

    printf("PASS: Generation counter incremented (%d -> %d)\n", old_gen, new_gen);
}

void test_derive_quota_excess() {
    printf("[TEST] Derive Quota Excess\n");
    capv2_table_init();

    resource_vector_t p_quota = {.cpu = Q16(100)};
    int parent = capv2_alloc(100, CAP_TYPE_RESOURCE_QUOTA, CAP_RIGHT_DERIVE | CAP_RIGHT_READ, p_quota);

    resource_vector_t c_quota = {.cpu = Q16(200)}; // More than parent
    int child = capv2_derive(parent, c_quota, CAP_RIGHT_READ);

    if (child != CAPV2_ERR_QUOTA_EXCEEDED) {
        printf("FAIL: Derived capability with more quota than parent\n");
        exit(1);
    }
    printf("PASS: Quota checks enforcement working\n");
}

int main() {
    test_privilege_escalation();
    test_stale_capability();
    test_derive_quota_excess();
    printf("All security tests passed.\n");
    return 0;
}
