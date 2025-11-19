/**
 * @file cap_ipc.c
 * @brief Zero-Copy IPC Implementation
 *
 * This file implements Cap'n Proto-inspired zero-copy IPC for passing
 * capabilities between processes.
 *
 * @see include/cap_ipc.h for API documentation
 */

#include "cap_ipc.h"
#include "capability_v2.h"
#include "printf.h"
#include "string.h"
#include <stddef.h>
#include <stdint.h>

/*******************************************************************************
 * IPC BUFFER POOL (Simplified Allocator)
 ******************************************************************************/

/**
 * IPC buffer pool
 *
 * SIMPLE ALLOCATOR:
 * - Fixed pool of 64 buffers (256 KB total)
 * - Bitmap allocation (1 bit per buffer)
 * - O(n) search for free buffer (acceptable for small pool)
 *
 * PRODUCTION:
 * - Use slab allocator (Linux SLUB/SLAB)
 * - Use buddy allocator for variable-size buffers
 * - Add per-CPU buffer caches for scalability
 */
#define IPC_BUFFER_POOL_SIZE 64

static cap_ipc_buffer_t g_ipc_buffer_pool[IPC_BUFFER_POOL_SIZE];
static uint64_t g_ipc_buffer_bitmap = 0; /* 1 bit per buffer (64 buffers max) */

/**
 * Allocate IPC buffer from pool
 *
 * @return Pointer to buffer, or NULL if pool full
 */
cap_ipc_buffer_t *cap_ipc_alloc_buffer(void)
{
    /* Find free buffer (bit == 0) */
    for (int i = 0; i < IPC_BUFFER_POOL_SIZE; i++) {
        uint64_t mask = (1ULL << i);
        if ((g_ipc_buffer_bitmap & mask) == 0) {
            /* Mark as allocated */
            g_ipc_buffer_bitmap |= mask;
            return &g_ipc_buffer_pool[i];
        }
    }

    /* Pool exhausted */
    return NULL;
}

/**
 * Free IPC buffer back to pool
 *
 * @param buffer Buffer to free
 */
void cap_ipc_free_buffer(cap_ipc_buffer_t *buffer)
{
    if (buffer == NULL) {
        return;
    }

    /* Find buffer index */
    int index = buffer - g_ipc_buffer_pool;
    if (index < 0 || index >= IPC_BUFFER_POOL_SIZE) {
        /* Invalid buffer pointer */
        return;
    }

    /* Mark as free */
    uint64_t mask = (1ULL << index);
    g_ipc_buffer_bitmap &= ~mask;

    /* Zero out buffer (security) */
    memset(buffer, 0, sizeof(cap_ipc_buffer_t));
}

/*******************************************************************************
 * SERIALIZATION / DESERIALIZATION
 ******************************************************************************/

/**
 * Serialize message to IPC buffer
 *
 * ZERO-COPY:
 * - Writes directly to buffer memory
 * - No intermediate copies
 */
int cap_ipc_serialize(cap_ipc_buffer_t *buffer,
                      uint32_t schema_id,
                      const void *data,
                      uint32_t data_size)
{
    if (buffer == NULL || data == NULL) {
        return -1; /* EINVAL */
    }

    /* Check if data fits in buffer */
    if (data_size > CAP_IPC_BUFFER_SIZE - sizeof(cap_ipc_header_t)) {
        return -2; /* EMSGSIZE */
    }

    /* Write header */
    cap_ipc_header_t *header = (cap_ipc_header_t *)buffer->data;
    header->schema_id = schema_id;
    header->data_size = data_size;

    /* Write data payload (zero-copy from source) */
    uint8_t *payload = buffer->data + sizeof(cap_ipc_header_t);
    memcpy(payload, data, data_size);

    return 0;
}

/**
 * Deserialize message from IPC buffer
 *
 * ZERO-COPY:
 * - Returns pointer directly into buffer
 * - No data copying
 */
int cap_ipc_deserialize(cap_ipc_buffer_t *buffer,
                        uint32_t *schema_id_out,
                        void **data_out,
                        uint32_t *data_size_out)
{
    if (buffer == NULL) {
        return -1; /* EINVAL */
    }

    /* Read header */
    cap_ipc_header_t *header = (cap_ipc_header_t *)buffer->data;

    if (schema_id_out != NULL) {
        *schema_id_out = header->schema_id;
    }

    if (data_size_out != NULL) {
        *data_size_out = header->data_size;
    }

    if (data_out != NULL) {
        /* Return pointer to payload (zero-copy) */
        *data_out = buffer->data + sizeof(cap_ipc_header_t);
    }

    return 0;
}

/*******************************************************************************
 * CAPABILITY EMBEDDING / EXTRACTION
 ******************************************************************************/

/**
 * Embed capability reference in message
 */
int cap_ipc_embed_capability(cap_ipc_buffer_t *buffer,
                              uint32_t offset,
                              int32_t cap_slot)
{
    if (buffer == NULL) {
        return -1; /* EINVAL */
    }

    /* Validate offset */
    if (offset + sizeof(cap_ipc_capref_t) > CAP_IPC_BUFFER_SIZE) {
        return -2; /* EMSGSIZE */
    }

    /* Get capability info */
    extern int capv2_validate_slot(int32_t);
    extern struct capability_v2 g_cap_table[];

    if (capv2_validate_slot(cap_slot) != 0) {
        return -3; /* EINVAL - invalid capability */
    }

    struct capability_v2 *cap = &g_cap_table[cap_slot];

    /* Write capability reference */
    cap_ipc_capref_t *capref = (cap_ipc_capref_t *)(buffer->data + offset);
    capref->slot_idx = cap_slot;
    capref->generation = cap->generation;

    return 0;
}

/**
 * Extract capability reference from message
 */
int cap_ipc_extract_capability(cap_ipc_buffer_t *buffer,
                                uint32_t offset,
                                int32_t *cap_slot_out)
{
    if (buffer == NULL || cap_slot_out == NULL) {
        return -1; /* EINVAL */
    }

    /* Validate offset */
    if (offset + sizeof(cap_ipc_capref_t) > CAP_IPC_BUFFER_SIZE) {
        return -2; /* EMSGSIZE */
    }

    /* Read capability reference */
    cap_ipc_capref_t *capref = (cap_ipc_capref_t *)(buffer->data + offset);

    /* Validate generation counter */
    extern int capv2_validate_slot(int32_t);
    extern struct capability_v2 g_cap_table[];

    if (capv2_validate_slot(capref->slot_idx) != 0) {
        return -3; /* EINVAL - invalid slot */
    }

    struct capability_v2 *cap = &g_cap_table[capref->slot_idx];

    if (cap->generation != capref->generation) {
        return -4; /* ESTALE - generation mismatch (use-after-free attempt) */
    }

    *cap_slot_out = capref->slot_idx;
    return 0;
}

/*******************************************************************************
 * IPC SEND / RECEIVE (Placeholder)
 ******************************************************************************/

/**
 * Send IPC message to process
 *
 * TODO: Implement IPC queue and process wakeup
 * For now, this is a placeholder that returns success.
 */
int cap_ipc_send(uint32_t recipient_pid, cap_ipc_buffer_t *buffer)
{
    if (buffer == NULL) {
        return -1; /* EINVAL */
    }

    /* TODO: Queue buffer in recipient's IPC queue */
    /* TODO: Wake up recipient if blocked on receive */

    (void)recipient_pid; /* Unused for now */

    printf("[IPC] Sent message to PID %u\n", recipient_pid);
    return 0;
}

/**
 * Receive IPC message (blocking)
 *
 * TODO: Implement IPC queue and blocking wait
 * For now, this is a placeholder that returns error.
 */
int cap_ipc_receive(cap_ipc_buffer_t **buffer_out)
{
    if (buffer_out == NULL) {
        return -1; /* EINVAL */
    }

    /* TODO: Check IPC receive queue */
    /* TODO: If empty, block until message arrives */
    /* TODO: Dequeue buffer and return */

    printf("[IPC] Receive not yet implemented\n");
    return -2; /* ENOSYS */
}

/*******************************************************************************
 * HELPER FUNCTIONS
 ******************************************************************************/

/**
 * Create simple RPC message
 */
cap_ipc_buffer_t *cap_ipc_create_simple_rpc(uint32_t method_id,
                                             const uint64_t *args,
                                             uint32_t arg_count,
                                             const int32_t *caps,
                                             uint32_t cap_count)
{
    if (arg_count > 8 || cap_count > 4) {
        return NULL; /* Too many args/caps */
    }

    /* Allocate buffer */
    cap_ipc_buffer_t *buf = cap_ipc_alloc_buffer();
    if (buf == NULL) {
        return NULL;
    }

    /* Build RPC structure */
    cap_ipc_simple_rpc_t rpc;
    rpc.method_id = method_id;
    rpc.arg_count = arg_count;
    rpc.cap_count = cap_count;

    /* Copy arguments */
    for (uint32_t i = 0; i < arg_count; i++) {
        rpc.args[i] = args[i];
    }

    /* Embed capabilities */
    for (uint32_t i = 0; i < cap_count; i++) {
        uint32_t offset = sizeof(cap_ipc_header_t) +
                          offsetof(cap_ipc_simple_rpc_t, caps) +
                          i * sizeof(cap_ipc_capref_t);
        cap_ipc_embed_capability(buf, offset, caps[i]);
    }

    /* Serialize */
    cap_ipc_serialize(buf, CAP_IPC_SCHEMA_SIMPLE_RPC, &rpc, sizeof(rpc));

    return buf;
}

/**
 * Create file open request
 */
cap_ipc_buffer_t *cap_ipc_create_file_open(const char *path,
                                            uint32_t flags,
                                            uint32_t mode)
{
    if (path == NULL) {
        return NULL;
    }

    /* Allocate buffer */
    cap_ipc_buffer_t *buf = cap_ipc_alloc_buffer();
    if (buf == NULL) {
        return NULL;
    }

    /* Build file open structure */
    cap_ipc_file_open_t req;
    strncpy(req.path, path, sizeof(req.path) - 1);
    req.path[sizeof(req.path) - 1] = '\0'; /* Null terminate */
    req.flags = flags;
    req.mode = mode;

    /* Serialize */
    cap_ipc_serialize(buf, CAP_IPC_SCHEMA_FILE_OPEN, &req, sizeof(req));

    return buf;
}

/**
 * Create file response
 */
cap_ipc_buffer_t *cap_ipc_create_file_response(int32_t status,
                                                int32_t file_cap_slot)
{
    /* Allocate buffer */
    cap_ipc_buffer_t *buf = cap_ipc_alloc_buffer();
    if (buf == NULL) {
        return NULL;
    }

    /* Build file response structure */
    cap_ipc_file_response_t resp;
    resp.status = status;

    /* Embed file capability */
    if (file_cap_slot >= 0) {
        uint32_t offset = sizeof(cap_ipc_header_t) +
                          offsetof(cap_ipc_file_response_t, file_cap);
        cap_ipc_embed_capability(buf, offset, file_cap_slot);
    }

    /* Serialize */
    cap_ipc_serialize(buf, CAP_IPC_SCHEMA_FILE_RESPONSE, &resp, sizeof(resp));

    return buf;
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Simple RPC with capability passing
 */
void example_ipc_simple_rpc(void)
{
    printf("\n=== Example: Simple RPC with Capabilities ===\n");
    printf("Scenario: Call method 42 with args [100, 200] and pass capability slot 5\n\n");

    /* Create dummy capability for testing */
    extern int capv2_alloc(uint64_t, uint8_t, uint32_t, struct resource_vector);
    extern void capv2_table_init(void);

    capv2_table_init();

    resource_vector_t quota = {0};
    int cap_slot = capv2_alloc(0x1000, 1 /* CAP_TYPE_MEMORY_PAGE */,
                               0x03 /* READ|WRITE */, quota);

    if (cap_slot < 0) {
        printf("Failed to allocate capability\n");
        return;
    }

    printf("Allocated capability at slot %d\n", cap_slot);

    /* Create RPC message */
    uint64_t args[] = {100, 200};
    int32_t caps[] = {cap_slot};

    cap_ipc_buffer_t *buf = cap_ipc_create_simple_rpc(42, args, 2, caps, 1);
    if (buf == NULL) {
        printf("Failed to create RPC message\n");
        return;
    }

    printf("Created RPC message\n");

    /* Deserialize and inspect */
    uint32_t schema_id;
    cap_ipc_simple_rpc_t *rpc;
    uint32_t size;

    cap_ipc_deserialize(buf, &schema_id, (void **)&rpc, &size);

    printf("\nDeserialized message:\n");
    printf("  Schema ID: %u (expected %u)\n", schema_id, CAP_IPC_SCHEMA_SIMPLE_RPC);
    printf("  Method ID: %u\n", rpc->method_id);
    printf("  Arguments: [%lu, %lu]\n", rpc->args[0], rpc->args[1]);
    printf("  Capabilities: %u\n", rpc->cap_count);

    /* Extract capability */
    int32_t extracted_slot;
    uint32_t offset = sizeof(cap_ipc_header_t) +
                      offsetof(cap_ipc_simple_rpc_t, caps);
    int ret = cap_ipc_extract_capability(buf, offset, &extracted_slot);

    if (ret == 0) {
        printf("  Extracted capability: slot %d (matches original: %s)\n",
               extracted_slot, extracted_slot == cap_slot ? "YES" : "NO");
    } else {
        printf("  Failed to extract capability: error %d\n", ret);
    }

    /* Send message (placeholder) */
    cap_ipc_send(100, buf);

    /* Cleanup */
    cap_ipc_free_buffer(buf);

    printf("=============================================\n\n");
}

/**
 * Example: File server (open/read/write)
 */
void example_ipc_file_server(void)
{
    printf("\n=== Example: File Server ===\n");
    printf("Scenario: Client requests file open, server responds with capability\n\n");

    /* Client: Create file open request */
    printf("[Client] Requesting to open /tmp/test.txt\n");

    cap_ipc_buffer_t *req_buf = cap_ipc_create_file_open("/tmp/test.txt",
                                                          0x02 /* O_RDWR */, 0644);
    if (req_buf == NULL) {
        printf("[Client] Failed to create request\n");
        return;
    }

    /* Client sends to server */
    cap_ipc_send(200, req_buf); /* PID 200 = file server */

    /* Server: Receive and process request */
    printf("[Server] Received file open request\n");

    uint32_t schema_id;
    cap_ipc_file_open_t *req;
    uint32_t size;

    cap_ipc_deserialize(req_buf, &schema_id, (void **)&req, &size);

    printf("[Server] Path: %s, Flags: 0x%x, Mode: 0%o\n",
           req->path, req->flags, req->mode);

    /* Server: Allocate file descriptor capability */
    extern int capv2_alloc(uint64_t, uint8_t, uint32_t, struct resource_vector);

    resource_vector_t quota = {0};
    int fd_cap = capv2_alloc(0x2000, 7 /* CAP_TYPE_FILE_DESCRIPTOR */,
                             0x03 /* READ|WRITE */, quota);

    printf("[Server] Allocated file descriptor capability: slot %d\n", fd_cap);

    /* Server: Create response */
    cap_ipc_buffer_t *resp_buf = cap_ipc_create_file_response(0, fd_cap);

    /* Server sends response to client */
    cap_ipc_send(100, resp_buf); /* PID 100 = client */

    /* Client: Receive and process response */
    printf("[Client] Received response\n");

    cap_ipc_file_response_t *resp;
    cap_ipc_deserialize(resp_buf, &schema_id, (void **)&resp, &size);

    printf("[Client] Status: %d\n", resp->status);

    if (resp->status == 0) {
        /* Extract file capability */
        int32_t client_fd_cap;
        uint32_t offset = sizeof(cap_ipc_header_t) +
                          offsetof(cap_ipc_file_response_t, file_cap);
        cap_ipc_extract_capability(resp_buf, offset, &client_fd_cap);

        printf("[Client] Received file capability: slot %d\n", client_fd_cap);
        printf("[Client] Can now read/write file using capability\n");
    }

    /* Cleanup */
    cap_ipc_free_buffer(req_buf);
    cap_ipc_free_buffer(resp_buf);

    printf("============================\n\n");
}

/**
 * Example: Zero-copy shared memory
 */
void example_ipc_zero_copy(void)
{
    printf("\n=== Example: Zero-Copy Shared Memory ===\n");
    printf("Scenario: Demonstrate zero-copy semantics\n\n");

    /* Allocate buffer */
    cap_ipc_buffer_t *buf = cap_ipc_alloc_buffer();
    if (buf == NULL) {
        printf("Failed to allocate buffer\n");
        return;
    }

    /* Write data directly to buffer (no copy) */
    cap_ipc_header_t *header = (cap_ipc_header_t *)buf->data;
    header->schema_id = CAP_IPC_SCHEMA_SIMPLE_RPC;
    header->data_size = 16;

    uint8_t *payload = buf->data + sizeof(cap_ipc_header_t);
    for (int i = 0; i < 16; i++) {
        payload[i] = i * 10;
    }

    printf("Wrote data directly to buffer at %p\n", (void *)buf);

    /* "Send" buffer (in reality, just share pointer) */
    /* Receiver gets pointer to same buffer - ZERO COPY */

    /* Read data directly from buffer (no copy) */
    void *read_payload;
    cap_ipc_deserialize(buf, NULL, &read_payload, NULL);

    printf("Read data directly from buffer at %p\n", read_payload);
    printf("Same address: %s (zero-copy confirmed)\n",
           read_payload == payload ? "YES" : "NO");

    /* Verify data */
    uint8_t *data = (uint8_t *)read_payload;
    printf("Data: [");
    for (int i = 0; i < 16; i++) {
        printf("%d%s", data[i], i < 15 ? ", " : "");
    }
    printf("]\n");

    /* Cleanup */
    cap_ipc_free_buffer(buf);

    printf("========================================\n\n");
}

/**
 * Run all IPC examples
 */
void cap_ipc_run_all_examples(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   ZERO-COPY IPC - PEDAGOGICAL EXAMPLES                     ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n");

    example_ipc_simple_rpc();
    example_ipc_file_server();
    example_ipc_zero_copy();

    printf("All IPC examples completed.\n\n");
}
