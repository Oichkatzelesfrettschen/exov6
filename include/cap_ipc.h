/**
 * @file cap_ipc.h
 * @brief Cap'n Proto-Inspired Zero-Copy IPC for Capabilities
 *
 * This file defines a simplified Cap'n Proto-style serialization format
 * for passing capabilities between processes with zero-copy semantics.
 *
 * THEORETICAL FOUNDATION:
 * - Cap'n Proto: Encoding-neutral RPC protocol
 * - Zero-copy: Data shared via pointers, not copied
 * - Type safety: Schema IDs prevent type confusion
 * - Arena allocation: Single buffer for message and capabilities
 *
 * DESIGN PRINCIPLES:
 * 1. ZERO-COPY: Message data stays in shared memory
 * 2. TYPE-SAFE: Schema IDs validate message format
 * 3. CAPABILITY-AWARE: Can embed capability references in messages
 * 4. SIMPLE: Simplified subset of Cap'n Proto for kernel use
 *
 * REAL-WORLD COMPARISON:
 * - Cap'n Proto: Full-featured RPC with schema compiler
 * - Our approach: Kernel-friendly subset (no allocations, fixed schemas)
 * - seL4: Passes capabilities in IPC registers
 * - Our hybrid: Passes capabilities in shared memory buffers
 *
 * PEDAGOGICAL NOTES:
 * This demonstrates how modern IPC systems (Cap'n Proto, gRPC) can be
 * adapted for kernel-level use with zero-copy semantics.
 *
 * @see kernel/cap_ipc.c for implementation
 * @see docs/PDAC_UNIFIED_FRAMEWORK.md for theoretical background
 */

#ifndef CAP_IPC_H
#define CAP_IPC_H

#include <stdint.h>
#include "capability_v2.h"

/*******************************************************************************
 * SERIALIZATION FORMAT
 ******************************************************************************/

/**
 * Message header (8 bytes)
 *
 * LAYOUT:
 * - schema_id (4 bytes): Type identifier for message format
 * - data_size (4 bytes): Size of data payload in bytes
 *
 * FOLLOWS:
 * - Data payload (data_size bytes)
 * - Capability slots (variable, based on schema)
 */
typedef struct {
    uint32_t schema_id;   /* Message type identifier */
    uint32_t data_size;   /* Size of data payload (bytes) */
} cap_ipc_header_t;

/**
 * Capability reference (embedded in messages)
 *
 * LAYOUT:
 * - slot_idx (4 bytes): Capability table slot index
 * - generation (4 bytes): Generation counter (for ABA protection)
 *
 * USAGE:
 * When a message contains a capability, it embeds this structure.
 * Receiver validates generation counter to prevent use-after-free.
 */
typedef struct {
    int32_t slot_idx;     /* Capability slot index */
    uint32_t generation;  /* Generation counter */
} cap_ipc_capref_t;

/**
 * IPC buffer (shared memory region)
 *
 * MEMORY LAYOUT:
 * +-------------------+
 * | cap_ipc_header_t  | (8 bytes)
 * +-------------------+
 * | Data payload      | (data_size bytes)
 * +-------------------+
 * | Capability refs   | (variable size)
 * +-------------------+
 *
 * ZERO-COPY SEMANTICS:
 * - Buffer allocated in shared memory region
 * - Sender writes message to buffer
 * - Receiver gets pointer to buffer (no copy)
 * - Receiver validates header and extracts capabilities
 */
#define CAP_IPC_BUFFER_SIZE 4096  /* 4 KB per buffer */

typedef struct {
    uint8_t data[CAP_IPC_BUFFER_SIZE];
} cap_ipc_buffer_t;

/*******************************************************************************
 * SCHEMA DEFINITIONS
 ******************************************************************************/

/**
 * Schema IDs (type identifiers)
 *
 * Each schema defines a message format. Receiver validates schema_id
 * to ensure type safety.
 *
 * EXTENSIBILITY:
 * Add new schemas here as needed. Schema compiler (future work) could
 * generate these from .capnp files.
 */
typedef enum {
    CAP_IPC_SCHEMA_NULL = 0,          /* Invalid/empty message */
    CAP_IPC_SCHEMA_SIMPLE_RPC,        /* Simple RPC: method_id + args */
    CAP_IPC_SCHEMA_FILE_OPEN,         /* File open request */
    CAP_IPC_SCHEMA_FILE_RESPONSE,     /* File open response (with cap) */
    CAP_IPC_SCHEMA_MEMORY_MAP,        /* Memory mapping request */
    CAP_IPC_SCHEMA_DEVICE_CONTROL,    /* Device I/O control */
    CAP_IPC_SCHEMA_CAP_GRANT,         /* Capability grant message */
    CAP_IPC_SCHEMA_CAP_REVOKE,        /* Capability revoke message */
} cap_ipc_schema_id_t;

/*******************************************************************************
 * MESSAGE STRUCTURES (Concrete Schemas)
 ******************************************************************************/

/**
 * Simple RPC message
 *
 * SCHEMA: CAP_IPC_SCHEMA_SIMPLE_RPC
 *
 * LAYOUT:
 * - header: cap_ipc_header_t
 * - method_id: uint32_t (RPC method to call)
 * - arg_count: uint32_t (number of arguments)
 * - args: uint64_t[arg_count] (arguments)
 * - cap_count: uint32_t (number of capabilities)
 * - caps: cap_ipc_capref_t[cap_count] (capability references)
 *
 * EXAMPLE: Call method 42 with args [100, 200] and capability slot 5
 */
typedef struct {
    uint32_t method_id;   /* RPC method identifier */
    uint32_t arg_count;   /* Number of arguments */
    uint64_t args[8];     /* Arguments (max 8) */
    uint32_t cap_count;   /* Number of capabilities */
    cap_ipc_capref_t caps[4]; /* Capability references (max 4) */
} cap_ipc_simple_rpc_t;

/**
 * File open request
 *
 * SCHEMA: CAP_IPC_SCHEMA_FILE_OPEN
 *
 * LAYOUT:
 * - path: char[256] (file path)
 * - flags: uint32_t (open flags: O_RDONLY, O_RDWR, etc.)
 * - mode: uint32_t (permissions for newly created files)
 *
 * RESPONSE: CAP_IPC_SCHEMA_FILE_RESPONSE with file descriptor capability
 */
typedef struct {
    char path[256];       /* File path */
    uint32_t flags;       /* Open flags (O_RDONLY, O_RDWR, O_CREAT, etc.) */
    uint32_t mode;        /* Permission mode (for O_CREAT) */
} cap_ipc_file_open_t;

/**
 * File open response
 *
 * SCHEMA: CAP_IPC_SCHEMA_FILE_RESPONSE
 *
 * LAYOUT:
 * - status: int32_t (0 on success, negative errno on failure)
 * - file_cap: cap_ipc_capref_t (capability reference to file descriptor)
 *
 * USAGE: Server responds with file descriptor capability
 */
typedef struct {
    int32_t status;       /* Return status (0 = success, <0 = errno) */
    cap_ipc_capref_t file_cap; /* File descriptor capability */
} cap_ipc_file_response_t;

/**
 * Capability grant message
 *
 * SCHEMA: CAP_IPC_SCHEMA_CAP_GRANT
 *
 * LAYOUT:
 * - source_cap: cap_ipc_capref_t (capability being granted)
 * - attenuated_rights: uint32_t (rights for recipient)
 * - recipient_pid: uint32_t (target process ID)
 *
 * USAGE: Explicitly grant capability to another process
 */
typedef struct {
    cap_ipc_capref_t source_cap;  /* Capability to grant */
    uint32_t attenuated_rights;   /* Rights for recipient */
    uint32_t recipient_pid;       /* Target process */
} cap_ipc_cap_grant_t;

/*******************************************************************************
 * IPC OPERATIONS
 ******************************************************************************/

/**
 * Allocate IPC buffer
 *
 * @return Pointer to IPC buffer, or NULL on failure
 *
 * IMPLEMENTATION:
 * - Allocates buffer from kernel IPC buffer pool
 * - Buffer can be shared between processes
 * - Caller must free with cap_ipc_free_buffer()
 *
 * TODO: Implement buffer pool allocator
 */
cap_ipc_buffer_t *cap_ipc_alloc_buffer(void);

/**
 * Free IPC buffer
 *
 * @param buffer Buffer to free
 *
 * IMPLEMENTATION:
 * - Returns buffer to kernel IPC buffer pool
 * - Buffer must not be accessed after free
 */
void cap_ipc_free_buffer(cap_ipc_buffer_t *buffer);

/**
 * Serialize message to IPC buffer
 *
 * @param buffer Target buffer
 * @param schema_id Schema identifier
 * @param data Data payload (schema-specific structure)
 * @param data_size Size of data payload in bytes
 * @return 0 on success, negative errno on failure
 *
 * ALGORITHM:
 * 1. Write header (schema_id, data_size)
 * 2. Write data payload
 * 3. Return buffer pointer (zero-copy)
 *
 * EXAMPLE:
 * ```c
 * cap_ipc_buffer_t *buf = cap_ipc_alloc_buffer();
 * cap_ipc_simple_rpc_t rpc = {.method_id = 42, .arg_count = 2, ...};
 * cap_ipc_serialize(buf, CAP_IPC_SCHEMA_SIMPLE_RPC, &rpc, sizeof(rpc));
 * ```
 */
int cap_ipc_serialize(cap_ipc_buffer_t *buffer,
                      uint32_t schema_id,
                      const void *data,
                      uint32_t data_size);

/**
 * Deserialize message from IPC buffer
 *
 * @param buffer Source buffer
 * @param schema_id_out Output: schema ID (may be NULL)
 * @param data_out Output: pointer to data payload (may be NULL)
 * @param data_size_out Output: size of data payload (may be NULL)
 * @return 0 on success, negative errno on failure
 *
 * ALGORITHM:
 * 1. Read header
 * 2. Validate schema_id
 * 3. Return pointer to data (zero-copy)
 *
 * ZERO-COPY:
 * data_out points directly into buffer (no copy)
 *
 * EXAMPLE:
 * ```c
 * uint32_t schema_id;
 * cap_ipc_simple_rpc_t *rpc;
 * uint32_t size;
 * cap_ipc_deserialize(buf, &schema_id, (void **)&rpc, &size);
 *
 * if (schema_id == CAP_IPC_SCHEMA_SIMPLE_RPC) {
 *     // Process RPC
 *     handle_rpc(rpc);
 * }
 * ```
 */
int cap_ipc_deserialize(cap_ipc_buffer_t *buffer,
                        uint32_t *schema_id_out,
                        void **data_out,
                        uint32_t *data_size_out);

/**
 * Send IPC message to process
 *
 * @param recipient_pid Target process ID
 * @param buffer Message buffer
 * @return 0 on success, negative errno on failure
 *
 * ALGORITHM:
 * 1. Validate recipient PID
 * 2. Queue buffer in recipient's IPC receive queue
 * 3. Wake up recipient if blocked
 *
 * ZERO-COPY:
 * Buffer is shared (not copied) to recipient
 *
 * TODO: Implement IPC queue and wakeup mechanism
 */
int cap_ipc_send(uint32_t recipient_pid, cap_ipc_buffer_t *buffer);

/**
 * Receive IPC message (blocking)
 *
 * @param buffer_out Output: received buffer
 * @return 0 on success, negative errno on failure
 *
 * ALGORITHM:
 * 1. Check IPC receive queue
 * 2. If empty, block until message arrives
 * 3. Dequeue buffer and return
 *
 * BLOCKING:
 * If no messages available, caller blocks until message arrives
 *
 * TODO: Implement blocking wait and wakeup
 */
int cap_ipc_receive(cap_ipc_buffer_t **buffer_out);

/**
 * Embed capability in message
 *
 * @param buffer Message buffer
 * @param offset Offset in buffer to write capability reference
 * @param cap_slot Capability slot to embed
 * @return 0 on success, negative errno on failure
 *
 * ALGORITHM:
 * 1. Get capability from table
 * 2. Write cap_ipc_capref_t to buffer at offset
 * 3. Capability remains in sender's table (reference only)
 *
 * USAGE:
 * Embed capability reference in message payload.
 * Receiver can extract and validate capability.
 *
 * EXAMPLE:
 * ```c
 * cap_ipc_buffer_t *buf = cap_ipc_alloc_buffer();
 * cap_ipc_file_response_t response;
 * response.status = 0;
 * cap_ipc_embed_capability(buf, offsetof(cap_ipc_file_response_t, file_cap), fd_cap_slot);
 * cap_ipc_serialize(buf, CAP_IPC_SCHEMA_FILE_RESPONSE, &response, sizeof(response));
 * ```
 */
int cap_ipc_embed_capability(cap_ipc_buffer_t *buffer,
                              uint32_t offset,
                              int32_t cap_slot);

/**
 * Extract capability from message
 *
 * @param buffer Message buffer
 * @param offset Offset in buffer to read capability reference
 * @param cap_slot_out Output: capability slot index
 * @return 0 on success, negative errno on failure
 *
 * ALGORITHM:
 * 1. Read cap_ipc_capref_t from buffer at offset
 * 2. Validate generation counter
 * 3. Return slot index
 *
 * SECURITY:
 * Validates generation counter to prevent use-after-free attacks
 *
 * EXAMPLE:
 * ```c
 * int32_t fd_slot;
 * cap_ipc_extract_capability(buf, offsetof(cap_ipc_file_response_t, file_cap), &fd_slot);
 * // Now use fd_slot to access file capability
 * ```
 */
int cap_ipc_extract_capability(cap_ipc_buffer_t *buffer,
                                uint32_t offset,
                                int32_t *cap_slot_out);

/*******************************************************************************
 * HELPER FUNCTIONS
 ******************************************************************************/

/**
 * Create simple RPC message
 *
 * @param method_id RPC method identifier
 * @param args Arguments array (max 8)
 * @param arg_count Number of arguments
 * @param caps Capability slots to pass (max 4)
 * @param cap_count Number of capabilities
 * @return IPC buffer with serialized message, or NULL on failure
 *
 * CONVENIENCE FUNCTION:
 * Combines allocation, serialization, and capability embedding.
 */
cap_ipc_buffer_t *cap_ipc_create_simple_rpc(uint32_t method_id,
                                             const uint64_t *args,
                                             uint32_t arg_count,
                                             const int32_t *caps,
                                             uint32_t cap_count);

/**
 * Create file open request
 *
 * @param path File path (max 255 chars)
 * @param flags Open flags (O_RDONLY, O_RDWR, etc.)
 * @param mode Permission mode (for O_CREAT)
 * @return IPC buffer with serialized message, or NULL on failure
 */
cap_ipc_buffer_t *cap_ipc_create_file_open(const char *path,
                                            uint32_t flags,
                                            uint32_t mode);

/**
 * Create file response
 *
 * @param status Return status (0 = success, <0 = errno)
 * @param file_cap_slot File descriptor capability slot
 * @return IPC buffer with serialized message, or NULL on failure
 */
cap_ipc_buffer_t *cap_ipc_create_file_response(int32_t status,
                                                int32_t file_cap_slot);

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Simple RPC with capability passing
 *
 * DEMONSTRATES: How to send RPC message with embedded capabilities
 */
void example_ipc_simple_rpc(void);

/**
 * Example: File server (open/read/write)
 *
 * DEMONSTRATES: Request-response pattern with capability delegation
 */
void example_ipc_file_server(void);

/**
 * Example: Zero-copy shared memory
 *
 * DEMONSTRATES: How to share large data structures without copying
 */
void example_ipc_zero_copy(void);

/**
 * Run all IPC examples
 */
void cap_ipc_run_all_examples(void);

#endif /* CAP_IPC_H */
