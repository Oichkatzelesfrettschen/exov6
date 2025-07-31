/*
 * @file    cap_table.c
 * @brief   Unified capability table management, stubs for authentication and DAG checks.
 *
 * Provides:
 *  - cap_table_init / alloc / lookup / refcount / revoke / validate
 *  - Stub implementations for octonion‐based and lattice‐based authentication
 *  - Simple DFS cycle detection for DAGs
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
#include <stdbool.h>
#include <string.h>
#include <stdatomic.h>

/*------------------------------------------------------------------------------
 * Global state
 *----------------------------------------------------------------------------*/
static struct spinlock      cap_lock;
static struct cap_entry     cap_table[CAP_MAX];
static atomic_uint_fast64_t global_epoch = ATOMIC_VAR_INIT(1);
static bool                 cap_table_ready = false;

/*------------------------------------------------------------------------------
 * System octonion key stub
 *----------------------------------------------------------------------------*/
static const octonion_t SYSTEM_OCTONION_KEY = {
    .e0 = 0.123, .e1 = 0.456, .e2 = 0.789, .e3 = 0.101,
    .e4 = 0.112, .e5 = 0.131, .e6 = 0.415, .e7 = 0.161
};

/*------------------------------------------------------------------------------
 * Helpers for cap_id encoding/decoding
 *----------------------------------------------------------------------------*/
static uint16_t get_index(cap_id_t id)   { return (uint16_t)(id & 0xFFFFu); }
static uint64_t get_epoch(cap_id_t id)   { return (uint64_t)(id >> 16); }
static cap_id_t generate_id(uint16_t i, uint64_t ep) {
    return (cap_id_t)((ep << 16) | i);
}

/*------------------------------------------------------------------------------
 * Octonion‐based authentication stub
 *----------------------------------------------------------------------------*/
static void generate_octonion_token(const struct cap_entry *e, octonion_t *out) {
    if (!e || !out) return;
    octonion_t tmp = {
        .e0 = e->id + 0.1,
        .e1 = e->epoch + 0.2,
        .e2 = e->type + 0.3,
        .e3 = e->rights_mask + 0.4,
        .e4 = (uintptr_t)e->resource_ptr + 0.5,
        .e5 = (uintptr_t)e->access_path_ptr + 0.6,
        .e6 = e->owner + 0.7,
        .e7 = e->generation + 0.8
    };
    *out = octonion_multiply(tmp, SYSTEM_OCTONION_KEY);
    octonion_t key2 = octonion_multiply(SYSTEM_OCTONION_KEY, SYSTEM_OCTONION_KEY);
    *out = octonion_multiply(*out, key2);
}

static bool verify_octonion_token(const struct cap_entry *e, const octonion_t *t) {
    if (!e || !t) return false;
    octonion_t expected;
    generate_octonion_token(e, &expected);
    return octonion_equals(&expected, t);
}

/*------------------------------------------------------------------------------
 * Lattice‐based signature stub
 *----------------------------------------------------------------------------*/
static void generate_lattice_sig(const struct cap_entry *e, lattice_sig_t *out) {
    if (!e || !out) return;
    uint8_t digest[8] = {
        (uint8_t)( e->id         & 0xFFu),
        (uint8_t)((e->id >> 8 ) & 0xFFu),
        (uint8_t)( e->epoch      & 0xFFu),
        (uint8_t)( e->type       & 0xFFu),
        (uint8_t)( e->rights_mask& 0xFFu),
        (uint8_t)( e->owner      & 0xFFu),
        (uint8_t)((uintptr_t)e->resource_ptr     & 0xFFu),
        (uint8_t)((uintptr_t)e->access_path_ptr & 0xFFu)
    };
    memset(out->sig_data, 0xCC, LATTICE_SIG_BYTES);
    memcpy(out->sig_data, digest, sizeof digest);
    out->sig_size = LATTICE_SIG_BYTES;
}

static bool verify_lattice_sig(const struct cap_entry *e, const lattice_sig_t *s) {
    if (!e || !s || s->sig_size != LATTICE_SIG_BYTES) return false;
    uint8_t expected[8];
    for (int i = 0; i < 8; i++) expected[i] = ((uint8_t *)&e->id)[i];
    if (memcmp(s->sig_data, expected, sizeof expected) != 0) return false;
    for (size_t i = sizeof expected; i < s->sig_size; ++i) {
        if (s->sig_data[i] != 0xCC) return false;
    }
    return true;
}

/*------------------------------------------------------------------------------
 * DAG cycle detection
 *----------------------------------------------------------------------------*/
static bool dfs_cycle(struct dag_node *n, struct dag_node **stk, size_t depth) {
    for (size_t i = 0; i < depth; ++i) {
        if (stk[i] == n) return true;
    }
    stk[depth] = n;
    for (struct dag_node_list *l = n->children; l; l = l->next) {
        if (dfs_cycle(l->node, stk, depth+1)) return true;
    }
    return false;
}

static bool verify_acyclic(const struct dag_node *start) {
    if (!start) return true;
    struct dag_node *stack[DAG_MAX_DEPTH] = { NULL };
    return !dfs_cycle((struct dag_node *)start, stack, 0);
}

/*------------------------------------------------------------------------------
 * Capability table API
 *----------------------------------------------------------------------------*/
void cap_table_init(void) {
    initlock(&cap_lock, "cap_table");
    memset(cap_table, 0, sizeof cap_table);
    atomic_store(&global_epoch, 1);
    cap_table_ready = true;
}

cap_id_t cap_table_alloc(cap_type_t type, void *res, uint64_t rights,
                         uint32_t owner, struct dag_node *path,
                         const lattice_pt *lat, bool qsafe) {
    if (!cap_table_ready || type == CAP_TYPE_NONE) return 0;
    acquire(&cap_lock);
    for (uint16_t i = 1; i < CAP_MAX; i++) {
        struct cap_entry *e = &cap_table[i];
        if (e->type == CAP_TYPE_NONE) {
            e->epoch   = atomic_load(&global_epoch);
            e->generation = 0;
            e->id      = generate_id(i, e->epoch);
            e->type    = type;
            e->resource_ptr = res;
            e->rights_mask = rights;
            e->owner   = owner;
            e->access_path_ptr = path;
            if (lat) e->resource_identifier_lattice = *lat;
            else     memset(&e->resource_identifier_lattice,0,sizeof e->resource_identifier_lattice);
            if (qsafe) {
                generate_lattice_sig(e, &e->auth.lattice_auth_signature);
                e->flags.quantum_safe = 1;
            } else {
                generate_octonion_token(e, &e->auth.auth_token);
                e->flags.quantum_safe = 0;
            }
            e->flags.epoch_valid = 1;
            e->flags.dag_verified = 0;
            e->flags.crypto_verified = 0;
            atomic_store(&e->refcnt, 1);
            release(&cap_lock);
            return e->id;
        }
    }
    release(&cap_lock);
    return 0;
}

int cap_table_lookup(cap_id_t id, struct cap_entry *out) {
    if (!cap_table_ready || id == 0) return -1;
    uint16_t idx = get_index(id);
    uint64_t ep = get_epoch(id);
    if (idx==0 || idx>=CAP_MAX) return -1;
    acquire(&cap_lock);
    struct cap_entry e = cap_table[idx];
    if (e.type==CAP_TYPE_NONE || e.epoch!=ep) {
        release(&cap_lock);
        return -1;
    }
    if (out) *out = e;
    release(&cap_lock);
    return 0;
}

void cap_table_inc_ref(cap_id_t id) {
    if (!cap_table_ready || id==0) return;
    uint16_t idx = get_index(id);
    uint64_t ep = get_epoch(id);
    if (idx==0||idx>=CAP_MAX) return;
    acquire(&cap_lock);
    struct cap_entry *e = &cap_table[idx];
    if (e->type!=CAP_TYPE_NONE && e->epoch==ep) {
        atomic_fetch_add(&e->refcnt,1);
    }
    release(&cap_lock);
}

void cap_table_dec_ref(cap_id_t id) {
    if (!cap_table_ready || id==0) return;
    uint16_t idx = get_index(id);
    uint64_t ep = get_epoch(id);
    if (idx==0||idx>=CAP_MAX) return;
    acquire(&cap_lock);
    struct cap_entry *e = &cap_table[idx];
    if (e->type!=CAP_TYPE_NONE && e->epoch==ep &&
        atomic_fetch_sub(&e->refcnt,1)==1) {
        e->type = CAP_TYPE_NONE;
        e->resource_ptr = NULL;
        e->access_path_ptr = NULL;
        memset(&e->resource_identifier_lattice,0,sizeof e->resource_identifier_lattice);
        memset(&e->auth,0,sizeof e->auth);
        memset(&e->flags,0,sizeof e->flags);
        e->owner = 0;
        e->rights_mask = 0;
    }
    release(&cap_lock);
}

int cap_revoke(cap_id_t id) {
    if (!cap_table_ready || id==0) return -1;
    uint16_t idx = get_index(id);
    uint64_t ep = get_epoch(id);
    if (idx==0||idx>=CAP_MAX) return -1;
    acquire(&cap_lock);
    struct cap_entry *e = &cap_table[idx];
    if (e->type==CAP_TYPE_NONE || e->epoch!=ep) {
        release(&cap_lock);
        return -1;
    }
    if (e->epoch == UINT64_MAX) {
        release(&cap_lock);
        return -2;
    }
    e->epoch++;
    atomic_store(&e->refcnt,0);
    e->type = CAP_TYPE_NONE;
    /* clear fields */
    e->resource_ptr = NULL; e->access_path_ptr = NULL;
    memset(&e->resource_identifier_lattice,0,sizeof e->resource_identifier_lattice);
    memset(&e->auth,0,sizeof e->auth);
    memset(&e->flags,0,sizeof e->flags);
    e->owner = 0; e->rights_mask = 0;
    /* bump global if needed */
    uint64_t g = atomic_load(&global_epoch);
    if (g <= e->epoch) atomic_store(&global_epoch,e->epoch+1);
    release(&cap_lock);
    return 0;
}

cap_validation_result_t cap_validate_unified(cap_id_t id, struct cap_entry *out) {
    if (!cap_table_ready) return VALIDATION_FAILED_NULL;
    uint16_t idx = get_index(id);
    uint64_t ep = get_epoch(id);
    if (idx==0||idx>=CAP_MAX) return VALIDATION_FAILED_NULL;
    acquire(&cap_lock);
    struct cap_entry e = cap_table[idx];
    if (e.type==CAP_TYPE_NONE || e.epoch!=ep) {
        release(&cap_lock);
        return VALIDATION_FAILED_NULL;
    }
    release(&cap_lock);
    if (e.access_path_ptr && !verify_acyclic(e.access_path_ptr))
        return VALIDATION_FAILED_DAG;
    if (e.flags.quantum_safe) {
        if (!verify_lattice_sig(&e,&e.auth.lattice_auth_signature))
            return VALIDATION_FAILED_CRYPTO_AUTH;
    } else {
        if (!verify_octonion_token(&e,&e.auth.auth_token))
            return VALIDATION_FAILED_CRYPTO_AUTH;
    }
    if (out) *out = e;
    return VALIDATION_SUCCESS;
}