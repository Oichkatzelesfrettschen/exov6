/**
 * @file test_token_bucket_and_ipc.c
 * @brief Unit Tests for Token Bucket and IPC Systems
 *
 * @see kernel/token_bucket.c
 * @see kernel/cap_ipc.c
 */

#include "capability_v2.h"
#include "cap_ipc.h"
#include "printf.h"
#include <stdint.h>
#include <string.h>

/*******************************************************************************
 * TEST FRAMEWORK
 ******************************************************************************/

static int g_tests_run = 0;
static int g_tests_passed = 0;
static int g_tests_failed = 0;

#define TEST_ASSERT(condition, message) \
    do { \
        if (!(condition)) { \
            printf("  FAIL: %s\n", message); \
            return -1; \
        } \
    } while (0)

#define TEST_ASSERT_EQ(actual, expected, message) \
    do { \
        if ((actual) != (expected)) { \
            printf("  FAIL: %s (expected %d, got %d)\n", message, (int)(expected), (int)(actual)); \
            return -1; \
        } \
    } while (0)

#define RUN_TEST(test_func) \
    do { \
        printf("\n[TEST] %s\n", #test_func); \
        g_tests_run++; \
        if (test_func() == 0) { \
            printf("  PASS\n"); \
            g_tests_passed++; \
        } else { \
            g_tests_failed++; \
        } \
    } while (0)

/*******************************************************************************
 * TOKEN BUCKET TESTS
 ******************************************************************************/

/**
 * Test: Token bucket initialization
 */
static int test_token_bucket_init(void)
{
    extern void token_bucket_init(struct token_bucket *, q16_t, q16_t);
    extern q16_t token_bucket_get_tokens(struct token_bucket *);

    struct token_bucket bucket;
    token_bucket_init(&bucket, Q16(100), Q16(10));

    TEST_ASSERT_EQ(bucket.capacity, Q16(100), "Capacity should match");
    TEST_ASSERT_EQ(bucket.refill_rate, Q16(10), "Refill rate should match");

    q16_t tokens = token_bucket_get_tokens(&bucket);
    TEST_ASSERT_EQ(tokens, Q16(100), "Should start with full bucket");

    return 0;
}

/**
 * Test: Token consumption
 */
static int test_token_bucket_consume(void)
{
    extern void token_bucket_init(struct token_bucket *, q16_t, q16_t);
    extern int token_bucket_consume(struct token_bucket *, q16_t);
    extern q16_t token_bucket_get_tokens(struct token_bucket *);

    struct token_bucket bucket;
    token_bucket_init(&bucket, Q16(100), Q16(10));

    /* Consume 50 tokens */
    int ret = token_bucket_consume(&bucket, Q16(50));
    TEST_ASSERT_EQ(ret, 1, "Should succeed (enough tokens)");

    q16_t remaining = token_bucket_get_tokens(&bucket);
    TEST_ASSERT_EQ(remaining, Q16(50), "Should have 50 tokens left");

    /* Try to consume 100 tokens (should fail, only 50 available) */
    ret = token_bucket_consume(&bucket, Q16(100));
    TEST_ASSERT_EQ(ret, 0, "Should fail (insufficient tokens)");

    return 0;
}

/**
 * Test: Token bucket reset
 */
static int test_token_bucket_reset(void)
{
    extern void token_bucket_init(struct token_bucket *, q16_t, q16_t);
    extern int token_bucket_consume(struct token_bucket *, q16_t);
    extern void token_bucket_reset(struct token_bucket *);
    extern q16_t token_bucket_get_tokens(struct token_bucket *);

    struct token_bucket bucket;
    token_bucket_init(&bucket, Q16(100), Q16(10));

    /* Consume all tokens */
    token_bucket_consume(&bucket, Q16(100));

    q16_t remaining = token_bucket_get_tokens(&bucket);
    TEST_ASSERT_EQ(remaining, 0, "Should have 0 tokens");

    /* Reset */
    token_bucket_reset(&bucket);

    remaining = token_bucket_get_tokens(&bucket);
    TEST_ASSERT_EQ(remaining, Q16(100), "Should be refilled to capacity");

    return 0;
}

/**
 * Test: Rate limit integration with capabilities
 */
static int test_rate_limit_integration(void)
{
    extern void capv2_table_init(void);
    extern int capv2_alloc(uint64_t, uint8_t, uint32_t, resource_vector_t);
    extern int capv2_enable_rate_limit(int, q16_t, q16_t);
    extern int capv2_check_rights_ratelimited(int, uint32_t, q16_t);

    capv2_table_init();

    resource_vector_t quota = {0};
    int slot = capv2_alloc(0x1000, 1, CAP_RIGHT_READ, quota);
    TEST_ASSERT(slot >= 0, "Allocation should succeed");

    /* Enable rate limiting: 10 tokens capacity, 1/sec refill */
    int ret = capv2_enable_rate_limit(slot, Q16(10), Q16(1));
    TEST_ASSERT_EQ(ret, 0, "Enable rate limit should succeed");

    /* Consume all 10 tokens */
    for (int i = 0; i < 10; i++) {
        ret = capv2_check_rights_ratelimited(slot, CAP_RIGHT_READ, Q16(1));
        TEST_ASSERT_EQ(ret, 0, "Should succeed while tokens available");
    }

    /* 11th access should be rate limited */
    ret = capv2_check_rights_ratelimited(slot, CAP_RIGHT_READ, Q16(1));
    TEST_ASSERT_EQ(ret, -7, "Should be rate limited (CAPV2_ERR_RATE_LIMITED)");

    return 0;
}

/*******************************************************************************
 * IPC TESTS
 ******************************************************************************/

/**
 * Test: IPC buffer allocation and free
 */
static int test_ipc_buffer_alloc(void)
{
    cap_ipc_buffer_t *buf1 = cap_ipc_alloc_buffer();
    TEST_ASSERT(buf1 != NULL, "First allocation should succeed");

    cap_ipc_buffer_t *buf2 = cap_ipc_alloc_buffer();
    TEST_ASSERT(buf2 != NULL, "Second allocation should succeed");
    TEST_ASSERT(buf1 != buf2, "Buffers should be different");

    cap_ipc_free_buffer(buf1);
    cap_ipc_free_buffer(buf2);

    /* Reallocate after free */
    buf1 = cap_ipc_alloc_buffer();
    TEST_ASSERT(buf1 != NULL, "Reallocation should succeed");

    cap_ipc_free_buffer(buf1);

    return 0;
}

/**
 * Test: IPC serialization and deserialization
 */
static int test_ipc_serialize_deserialize(void)
{
    cap_ipc_buffer_t *buf = cap_ipc_alloc_buffer();
    TEST_ASSERT(buf != NULL, "Allocation should succeed");

    /* Serialize a simple RPC message */
    cap_ipc_simple_rpc_t rpc;
    rpc.method_id = 42;
    rpc.arg_count = 2;
    rpc.args[0] = 100;
    rpc.args[1] = 200;
    rpc.cap_count = 0;

    int ret = cap_ipc_serialize(buf, CAP_IPC_SCHEMA_SIMPLE_RPC, &rpc, sizeof(rpc));
    TEST_ASSERT_EQ(ret, 0, "Serialization should succeed");

    /* Deserialize */
    uint32_t schema_id;
    cap_ipc_simple_rpc_t *rpc_out;
    uint32_t size;

    ret = cap_ipc_deserialize(buf, &schema_id, (void **)&rpc_out, &size);
    TEST_ASSERT_EQ(ret, 0, "Deserialization should succeed");
    TEST_ASSERT_EQ(schema_id, CAP_IPC_SCHEMA_SIMPLE_RPC, "Schema ID should match");
    TEST_ASSERT_EQ(rpc_out->method_id, 42, "Method ID should match");
    TEST_ASSERT_EQ(rpc_out->arg_count, 2, "Arg count should match");
    TEST_ASSERT_EQ(rpc_out->args[0], 100, "First arg should match");
    TEST_ASSERT_EQ(rpc_out->args[1], 200, "Second arg should match");

    /* Verify zero-copy (pointers should point into buffer) */
    uintptr_t buf_addr = (uintptr_t)buf->data;
    uintptr_t rpc_addr = (uintptr_t)rpc_out;
    TEST_ASSERT(rpc_addr >= buf_addr && rpc_addr < buf_addr + sizeof(cap_ipc_buffer_t),
                "Deserialized pointer should be inside buffer (zero-copy)");

    cap_ipc_free_buffer(buf);

    return 0;
}

/**
 * Test: Capability embedding and extraction
 */
static int test_ipc_capability_embed_extract(void)
{
    extern void capv2_table_init(void);
    extern int capv2_alloc(uint64_t, uint8_t, uint32_t, resource_vector_t);

    capv2_table_init();

    /* Allocate a capability */
    resource_vector_t quota = {0};
    int cap_slot = capv2_alloc(0xCAFE, 1, CAP_RIGHT_READ, quota);
    TEST_ASSERT(cap_slot >= 0, "Capability allocation should succeed");

    /* Allocate IPC buffer */
    cap_ipc_buffer_t *buf = cap_ipc_alloc_buffer();
    TEST_ASSERT(buf != NULL, "Buffer allocation should succeed");

    /* Embed capability */
    uint32_t offset = sizeof(cap_ipc_header_t);
    int ret = cap_ipc_embed_capability(buf, offset, cap_slot);
    TEST_ASSERT_EQ(ret, 0, "Embed should succeed");

    /* Extract capability */
    int32_t extracted_slot;
    ret = cap_ipc_extract_capability(buf, offset, &extracted_slot);
    TEST_ASSERT_EQ(ret, 0, "Extract should succeed");
    TEST_ASSERT_EQ(extracted_slot, cap_slot, "Extracted slot should match");

    cap_ipc_free_buffer(buf);

    return 0;
}

/**
 * Test: IPC generation counter validation (security)
 */
static int test_ipc_generation_validation(void)
{
    extern void capv2_table_init(void);
    extern int capv2_alloc(uint64_t, uint8_t, uint32_t, resource_vector_t);
    extern struct capability_v2 g_cap_table[];

    capv2_table_init();

    /* Allocate a capability */
    resource_vector_t quota = {0};
    int cap_slot = capv2_alloc(0x1000, 1, CAP_RIGHT_READ, quota);
    TEST_ASSERT(cap_slot >= 0, "Allocation should succeed");

    /* Embed capability */
    cap_ipc_buffer_t *buf = cap_ipc_alloc_buffer();
    uint32_t offset = sizeof(cap_ipc_header_t);
    cap_ipc_embed_capability(buf, offset, cap_slot);

    /* Tamper with generation counter in buffer (simulate attack) */
    cap_ipc_capref_t *capref = (cap_ipc_capref_t *)(buf->data + offset);
    capref->generation = 999; /* Invalid generation */

    /* Try to extract (should fail due to generation mismatch) */
    int32_t extracted_slot;
    int ret = cap_ipc_extract_capability(buf, offset, &extracted_slot);
    TEST_ASSERT_EQ(ret, -4, "Should fail with generation mismatch (ESTALE)");

    cap_ipc_free_buffer(buf);

    return 0;
}

/**
 * Test: Helper function (create_simple_rpc)
 */
static int test_ipc_create_simple_rpc(void)
{
    extern void capv2_table_init(void);
    extern int capv2_alloc(uint64_t, uint8_t, uint32_t, resource_vector_t);

    capv2_table_init();

    /* Create capability */
    resource_vector_t quota = {0};
    int cap_slot = capv2_alloc(0x1000, 1, CAP_RIGHT_READ, quota);
    TEST_ASSERT(cap_slot >= 0, "Capability allocation should succeed");

    /* Create RPC with capability */
    uint64_t args[] = {100, 200};
    int32_t caps[] = {cap_slot};

    cap_ipc_buffer_t *buf = cap_ipc_create_simple_rpc(42, args, 2, caps, 1);
    TEST_ASSERT(buf != NULL, "create_simple_rpc should succeed");

    /* Verify */
    uint32_t schema_id;
    cap_ipc_simple_rpc_t *rpc;
    cap_ipc_deserialize(buf, &schema_id, (void **)&rpc, NULL);

    TEST_ASSERT_EQ(schema_id, CAP_IPC_SCHEMA_SIMPLE_RPC, "Schema should match");
    TEST_ASSERT_EQ(rpc->method_id, 42, "Method ID should match");
    TEST_ASSERT_EQ(rpc->arg_count, 2, "Arg count should match");
    TEST_ASSERT_EQ(rpc->cap_count, 1, "Cap count should match");

    cap_ipc_free_buffer(buf);

    return 0;
}

/**
 * Test: File open/response workflow
 */
static int test_ipc_file_workflow(void)
{
    extern void capv2_table_init(void);
    extern int capv2_alloc(uint64_t, uint8_t, uint32_t, resource_vector_t);

    capv2_table_init();

    /* Create file open request */
    cap_ipc_buffer_t *req_buf = cap_ipc_create_file_open("/tmp/test.txt", 0x02, 0644);
    TEST_ASSERT(req_buf != NULL, "File open request creation should succeed");

    /* Verify request */
    uint32_t schema_id;
    cap_ipc_file_open_t *req;
    cap_ipc_deserialize(req_buf, &schema_id, (void **)&req, NULL);

    TEST_ASSERT_EQ(schema_id, CAP_IPC_SCHEMA_FILE_OPEN, "Schema should match");
    TEST_ASSERT(strcmp(req->path, "/tmp/test.txt") == 0, "Path should match");
    TEST_ASSERT_EQ(req->flags, 0x02, "Flags should match");
    TEST_ASSERT_EQ(req->mode, 0644, "Mode should match");

    /* Server allocates file capability */
    resource_vector_t quota = {0};
    int fd_cap = capv2_alloc(0x2000, 7, CAP_RIGHT_READ | CAP_RIGHT_WRITE, quota);
    TEST_ASSERT(fd_cap >= 0, "File descriptor allocation should succeed");

    /* Create response */
    cap_ipc_buffer_t *resp_buf = cap_ipc_create_file_response(0, fd_cap);
    TEST_ASSERT(resp_buf != NULL, "File response creation should succeed");

    /* Verify response */
    cap_ipc_file_response_t *resp;
    cap_ipc_deserialize(resp_buf, &schema_id, (void **)&resp, NULL);

    TEST_ASSERT_EQ(schema_id, CAP_IPC_SCHEMA_FILE_RESPONSE, "Schema should match");
    TEST_ASSERT_EQ(resp->status, 0, "Status should be success");

    /* Extract file capability */
    int32_t client_fd;
    uint32_t offset = sizeof(cap_ipc_header_t) + offsetof(cap_ipc_file_response_t, file_cap);
    int ret = cap_ipc_extract_capability(resp_buf, offset, &client_fd);
    TEST_ASSERT_EQ(ret, 0, "Capability extraction should succeed");
    TEST_ASSERT_EQ(client_fd, fd_cap, "File descriptor should match");

    cap_ipc_free_buffer(req_buf);
    cap_ipc_free_buffer(resp_buf);

    return 0;
}

/*******************************************************************************
 * TEST SUITE RUNNER
 ******************************************************************************/

void run_all_token_bucket_and_ipc_tests(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   TOKEN BUCKET & IPC - UNIT TESTS                          ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    printf("\n=== TOKEN BUCKET TESTS ===\n");
    RUN_TEST(test_token_bucket_init);
    RUN_TEST(test_token_bucket_consume);
    RUN_TEST(test_token_bucket_reset);
    RUN_TEST(test_rate_limit_integration);

    printf("\n=== IPC TESTS ===\n");
    RUN_TEST(test_ipc_buffer_alloc);
    RUN_TEST(test_ipc_serialize_deserialize);
    RUN_TEST(test_ipc_capability_embed_extract);
    RUN_TEST(test_ipc_generation_validation);
    RUN_TEST(test_ipc_create_simple_rpc);
    RUN_TEST(test_ipc_file_workflow);

    /* Summary */
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   TEST SUMMARY                                              ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");
    printf("Tests Run:    %d\n", g_tests_run);
    printf("Tests Passed: %d\n", g_tests_passed);
    printf("Tests Failed: %d\n", g_tests_failed);

    if (g_tests_failed == 0) {
        printf("\n✓ ALL TESTS PASSED\n\n");
    } else {
        printf("\n✗ SOME TESTS FAILED\n\n");
    }
}
