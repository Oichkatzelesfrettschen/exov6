#pragma once
#include "types.h"
#include "resource_vector.h"
#include "q16_fixed.h"
#include "exo_lock.h"

struct capability_v2;
typedef uint32_t (*cap_formula_t)(struct capability_v2 *cap, void *data);

typedef enum {
    CAP_TYPE_NULL = 0,
    CAP_TYPE_MEMORY_PAGE,
    CAP_TYPE_DEVICE_PORT,
    CAP_TYPE_IPC_ENDPOINT,
    CAP_TYPE_IRQ_HANDLER,
    CAP_TYPE_PROCESS_CONTROL,
    CAP_TYPE_RESOURCE_QUOTA,
    CAP_TYPE_FILE_DESCRIPTOR,
    CAP_TYPE_NETWORK_SOCKET,
} cap_type_t;

#define CAP_RIGHT_READ    (1 << 0)
#define CAP_RIGHT_WRITE   (1 << 1)
#define CAP_RIGHT_EXECUTE (1 << 2)
#define CAP_RIGHT_GRANT   (1 << 3)
#define CAP_RIGHT_REVOKE  (1 << 4)
#define CAP_RIGHT_DERIVE  (1 << 5)

struct token_bucket {
    uint64_t tokens;
    uint64_t capacity;
    uint64_t refill_rate;
    uint64_t last_refill_ms;
    uint32_t rng_seed;
};

struct capability_v2 {
    uint64_t resource_id;
    uint32_t owner_pid;
    uint32_t refcount;
    cap_type_t cap_type;
    uint32_t static_rights;
    resource_vector_t quota;
    resource_vector_t consumed;
    cap_formula_t rights_fn;
    void *formula_data;
    uint32_t schema_id;
    void *capnp_buffer;
    uint32_t buffer_size;
    struct token_bucket rate_limit;
    uint32_t generation;
    uint64_t creation_time;
    uint64_t access_count;
    int32_t parent_slot;
    struct qspinlock lock;
};

#define CAP_TABLE_V2_SIZE 4096

#define CAPV2_OK                 0
#define CAPV2_ERR_INVALID_SLOT  -1
#define CAPV2_ERR_NO_PERMISSION -2
#define CAPV2_ERR_TABLE_FULL    -3
#define CAPV2_ERR_REFCOUNT_OVERFLOW -4
#define CAPV2_ERR_INVALID_TYPE  -5
#define CAPV2_ERR_QUOTA_EXCEEDED -6
#define CAPV2_ERR_RATE_LIMITED  -7
#define CAPV2_ERR_GENERATION_MISMATCH -8
#define CAPV2_ERR_INVALID_DERIVE -9
#define CAPV2_ERR_NOT_FOUND     -10

void capv2_table_init(void);
int capv2_alloc(uint64_t resource_id, cap_type_t cap_type, uint32_t initial_rights, resource_vector_t quota);
int capv2_free(int cap_slot);
int capv2_grant(int cap_slot, uint32_t recipient_pid, uint32_t attenuated_rights);
int capv2_revoke(int cap_slot);
int capv2_derive(int parent_slot, resource_vector_t child_quota, uint32_t child_rights);
int capv2_check_rights(int cap_slot, uint32_t requested_rights);
int capv2_get_info(int cap_slot, struct capability_v2 *cap_out);
