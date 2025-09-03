# Analysis Report: `read_file` for `kernel/cap_table.c`

## Tool Call:
```
default_api.read_file(absolute_path = "/Users/eirikr/Documents/GitHub/exov6/kernel/cap_table.c")
```

## Output:
```c
/*
 * @file cap_table.c
 * @brief Unified capability table and authentication stubs (C23).
 */

#include "cap.h"
#include "types.h"
#include "defs.h"
#include "engine/kernel/spinlock.h"
#include "octonion.h"
#include "lattice_types.h"
#include "dag.h"

#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdatomic.h>
#include <stdbool.h>

/*------------------------------------------------------------------------------
 * Global state
 *----------------------------------------------------------------------------*/
static struct spinlock      cap_lock;
static struct cap_entry     cap_table[CAP_MAX];
static atomic_uint_fast64_t global_current_epoch = ATOMIC_VAR_INIT(1);
static bool                 cap_table_ready      = false;

/*------------------------------------------------------------------------------
 * System octonion key stub
 *----------------------------------------------------------------------------*/
static const octonion_t SYSTEM_OCTONION_KEY = {
    .r = 0.123, .i = 0.456, .j = 0.789, .k = 0.101,
    .l = 0.112, .m = 0.131, .n = 0.415, .o = 0.161
};

/*------------------------------------------------------------------------------
 * Pseudo‐random generator (non‐crypto; stub only)
 *----------------------------------------------------------------------------*/
static uint32_t
lcg_rand(void)
{
    static uint32_t seed = 123456789u;
    seed = seed * 1103515245u + 12345u;
    return seed;
}

/*------------------------------------------------------------------------------
 * Helpers for cap_id encoding/decoding
 *----------------------------------------------------------------------------*/
static uint16_t
get_index_from_id(cap_id_t id)
{
    return (uint16_t)(id & 0xFFFFu);
}

static uint64_t
get_epoch_from_id(cap_id_t id)
{
    return (uint64_t)(id >> 16);
}

static cap_id_t
generate_cap_id(uint16_t index, uint64_t epoch)
{
    return (cap_id_t)((epoch << 16) | index);
}

/*------------------------------------------------------------------------------
 * Authentication stubs
 *----------------------------------------------------------------------------*/
static void
generate_stub_auth_token(const struct cap_entry *entry,
                         octonion_t *out)
{
    if (!entry || !out) {
        return;
    }
    octonion_t tmp = {
        .r = entry->id + 0.1,
        .i = entry->epoch + 0.2,
        .j = entry->type + 0.3,
        .k = entry->rights_mask + 0.4,
        .l = (uintptr_t)entry->resource_ptr + 0.5,
        .m = (uintptr_t)entry->access_path_ptr + 0.6,
        .n = entry->owner + 0.7,
        .o = entry->generation + 0.8
    };
    *out = quaternion_multiply(tmp, SYSTEM_OCTONION_KEY);
    octonion_t key_sq = quaternion_multiply(SYSTEM_OCTONION_KEY,
                                            SYSTEM_OCTONION_KEY);
    *out = quaternion_multiply(*out, key_sq);
}

static bool
verify_stub_auth_token(const struct cap_entry *entry,
                       const octonion_t *token)
{
    if (!entry || !token) {
        return false;
    }
    octonion_t expected;
    generate_stub_auth_token(entry, &expected);
    return octonion_equals(token, &expected);
}

static void
generate_lattice_signature_stub(const struct cap_entry *entry,
                                lattice_sig_t *out)
{
    if (!entry || !out) {
        return;
    }
    uint8_t digest[8] = {
        (uint8_t)(entry->id & 0xFFu),
        (uint8_t)((entry->id >> 8) & 0xFFu),
        (uint8_t)(entry->epoch & 0xFFu),
        (uint8_t)(entry->type & 0xFFu),
        (uint8_t)(entry->rights_mask & 0xFFu),
        (uint8_t)(entry->owner & 0xFFu),
        (uint8_t)((uintptr_t)entry->resource_ptr & 0xFFu),
        (uint8_t)((uintptr_t)entry->access_path_ptr & 0xFFu)
    };
    memset(out->sig_data, 0xCC, LATTICE_SIG_BYTES);
    memcpy(out->sig_data, digest, sizeof digest);
    out->sig_size = LATTICE_SIG_BYTES;
}

static bool
verify_lattice_signature_stub(const struct cap_entry *entry,
                              const lattice_sig_t *sig)
{
    if (!entry || !sig || sig->sig_size != LATTICE_SIG_BYTES) {
        return false;
    }
    uint8_t expected[8] = {
        (uint8_t)(entry->id & 0xFFu),
        (uint8_t)((entry->id >> 8) & 0xFFu),
        (uint8_t)(entry->epoch & 0xFFu),
        (uint8_t)(entry->type & 0xFFu),
        (uint8_t)(entry->rights_mask & 0xFFu),
        (uint8_t)(entry->owner & 0xFFu),
        (uint8_t)((uintptr_t)entry->resource_ptr & 0xFFu),
        (uint8_t)((uintptr_t)entry->access_path_ptr & 0xFFu)
    };
    if (memcmp(sig->sig_data, expected, sizeof expected) != 0) {
        return false;
    }
    for (size_t i = sizeof expected; i < sig->sig_size; ++i) {
        if (sig->sig_data[i] != 0xCC) {
            return false;
        }
    }
    return true;
}

/*------------------------------------------------------------------------------
 * DAG cycle detection stub
 *----------------------------------------------------------------------------*/
static bool
dfs_cycle(struct dag_node *node,
          struct dag_node **stack,
          size_t depth)
{
    for (size_t i = 0; i < depth; ++i) {
        if (stack[i] == node) {
            return true;
        }
    }
    stack[depth] = node;
    for (struct dag_node_list *l = node->children; l; l = l->next) {
        if (dfs_cycle(l->node, stack, depth + 1)) {
            return true;
        }
    }
    return false;
}

static bool
verify_dag_acyclic(const struct dag_node *start)
{
    if (!start) {
        return true;
    }
    struct dag_node *stack[DAG_MAX_DEPTH] = { NULL };
    return !dfs_cycle((struct dag_node *)start, stack, 0);
}

/*------------------------------------------------------------------------------
 * Capability table management
 *----------------------------------------------------------------------------*/
void
cap_table_init(void)
{
    initlock(&cap_lock, "cap_table");
    memset(cap_table, 0, sizeof cap_table);
    atomic_store(&global_current_epoch, 1);
    cap_table_ready = true;
}

cap_id_t
cap_table_alloc(cap_type_t        type,
                void             *resource_ptr,
                uint64_t          rights,
                uint32_t          owner,
                struct dag_node  *access_path,
                const lattice_pt *lattice_id,
                bool              quantum_safe)
{
    if (!cap_table_ready || type == CAP_TYPE_NONE) {
        return 0;
    }
    acquire(&cap_lock);
    for (uint16_t i = 1; i < CAP_MAX; ++i) {
        struct cap_entry *e = &cap_table[i];
        if (e->type == CAP_TYPE_NONE) {
            e->epoch = atomic_load(&global_current_epoch);
            e->generation = 0;
            e->id = generate_cap_id(i, e->epoch);
            e->type = type;
            e->resource_ptr = resource_ptr;
            e->rights_mask = rights;
            e->owner = owner;
            e->access_path_ptr = access_path;
            if (lattice_id) {
                e->resource_identifier_lattice = *lattice_id;
            } else {
                memset(&e->resource_identifier_lattice, 0,
                       sizeof e->resource_identifier_lattice);
            }
            if (quantum_safe) {
                generate_lattice_signature_stub(e,
                    &e->auth.lattice_auth_signature);
                e->flags.quantum_safe = 1;
            } else {
                generate_stub_auth_token(e, &e->auth.auth_token);
                e->flags.quantum_safe = 0;
            }
            e->flags.epoch_valid      = 1;
            e->flags.dag_verified     = 0;
            e->flags.crypto_verified  = 0;
            atomic_store(&e->refcnt, 1);
            initlock(&e->lock, "cap_entry");
            release(&cap_lock);
            return e->id;
        }
    }
    release(&cap_lock);
    return 0;
}

int
cap_table_lookup(cap_id_t id,
                 struct cap_entry *out)
{
    if (!cap_table_ready || id == 0) {
        return -1;
    }
    uint16_t idx = get_index_from_id(id);
    uint64_t ep  = get_epoch_from_id(id);
    if (idx == 0 || idx >= CAP_MAX) {
        return -1;
    }
    acquire(&cap_lock);
    struct cap_entry entry = cap_table[idx];
    if (entry.type == CAP_TYPE_NONE || entry.epoch != ep) {
        release(&cap_lock);
        return -1;
    }
    if (out) {
        *out = entry;
    }
    release(&cap_lock);
    return 0;
}

void
cap_table_inc_ref(cap_id_t id)
{
    if (!cap_table_ready || id == 0) {
        return;
    }
    uint16_t idx = get_index_from_id(id);
    uint64_t ep  = get_epoch_from_id(id);
    if (idx == 0 || idx >= CAP_MAX) {
        return;
    }
    acquire(&cap_lock);
    struct cap_entry *e = &cap_table[idx];
    if (e->type != CAP_TYPE_NONE && e->epoch == ep) {
        atomic_fetch_add(&e->refcnt, 1);
    }
    release(&cap_lock);
}

void
cap_table_dec_ref(cap_id_t id)
{
    if (!cap_table_ready || id == 0) {
        return;
    }
    uint16_t idx = get_index_from_id(id);
    uint64_t ep  = get_epoch_from_id(id);
    if (idx == 0 || idx >= CAP_MAX) {
        return;
    }
    acquire(&cap_lock);
    struct cap_entry *e = &cap_table[idx];
    if (e->type != CAP_TYPE_NONE && e->epoch == ep &&
        atomic_fetch_sub(&e->refcnt, 1) == 1)
    {
        e->type               = CAP_TYPE_NONE;
        e->resource_ptr       = NULL;
        e->access_path_ptr    = NULL;
        memset(&e->resource_identifier_lattice, 0,
               sizeof e->resource_identifier_lattice);
        memset(&e->auth, 0, sizeof e->auth);
        memset(&e->flags, 0, sizeof e->flags);
        e->owner              = 0;
        e->rights_mask        = 0;
    }
    release(&cap_lock);
}

int
cap_revoke(cap_id_t id)
{
    if (!cap_table_ready || id == 0) {
        return -1;
    }
    uint16_t idx = get_index_from_id(id);
    uint64_t ep  = get_epoch_from_id(id);
    if (idx == 0 || idx >= CAP_MAX) {
        return -1;
    }
    acquire(&cap_lock);
    struct cap_entry *e = &cap_table[idx];
    if (e->type == CAP_TYPE_NONE || e->epoch != ep) {
        release(&cap_lock);
        return -1;
    }
    if (e->epoch == UINT64_MAX) {
        release(&cap_lock);
        return -2;
    }
    e->epoch++;
    atomic_store(&e->refcnt, 0);
    e->type               = CAP_TYPE_NONE;
    e->resource_ptr       = NULL;
    e->access_path_ptr    = NULL;
    memset(&e->resource_identifier_lattice, 0,
           sizeof e->resource_identifier_lattice);
    memset(&e->auth, 0, sizeof e->auth);
    memset(&e->flags, 0, sizeof e->flags);
    e->owner              = 0;
    e->rights_mask        = 0;
    uint64_t gc = atomic_load(&global_current_epoch);
    if (gc <= e->epoch) {
        atomic_store(&global_current_epoch, e->epoch + 1);
    }
    release(&cap_lock);
    return 0;
}

cap_validation_result_t
cap_validate_unified(cap_id_t id,
                     struct cap_entry *out)
{
    if (!cap_table_ready) {
        return VALIDATION_FAILED_NULL;
    }
    uint16_t idx = get_index_from_id(id);
    uint64_t ep  = get_epoch_from_id(id);
    if (idx == 0 || idx >= CAP_MAX) {
        return VALIDATION_FAILED_NULL;
    }
    acquire(&cap_lock);
    struct cap_entry entry = cap_table[idx];
    if (entry.type == CAP_TYPE_NONE || entry.epoch != ep) {
        release(&cap_lock);
        return VALIDATION_FAILED_NULL;
    }
    release(&cap_lock);
    if (entry.access_path_ptr && !verify_dag_acyclic(entry.access_path_ptr)) {
        return VALIDATION_FAILED_DAG;
    }
    if (entry.flags.quantum_safe) {
        if (!verify_lattice_signature_stub(&entry,
                                           &entry.auth.lattice_auth_signature))
        {
            return VALIDATION_FAILED_CRYPTO_AUTH;
        }
    } else {
        if (!verify_stub_auth_token(&entry, &entry.auth.auth_token)) {
            return VALIDATION_FAILED_CRYPTO_AUTH;
        }
    }
    if (out) {
        *out = entry;
    }
    return VALIDATION_SUCCESS;
}
```