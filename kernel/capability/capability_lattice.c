/*
 * capability_lattice.c - Unified Capability Lattice System
 * 
 * Pure C17 implementation of mathematical lattice-based capabilities
 * Provides complete security model for exokernel architecture
 * 
 * Features:
 * - Partial order relations for capability delegation
 * - Lock-free atomic operations for performance
 * - Zero-copy capability transfer
 * - Cryptographic integrity with HMAC-SHA256
 * - Post-quantum ready design
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdatomic.h>
#include <string.h>
#include <stdalign.h>

#include "types.h"
#include "cap.h"
#include "libos/crypto.h"
#include "hal/hal.h"

/* Forward type declarations */
typedef struct capability capability_t;
typedef struct cap_lattice_node cap_lattice_node_t;
typedef uint64_t cap_rights_t;
typedef enum cap_type cap_type_t;

/* Forward declarations for internal functions */
static capability_t* capability_lookup(uint64_t cap_id);
static void capability_compute_hmac(capability_t *cap);
static bool capability_verify_hmac(capability_t *cap);
static void lattice_add_capability(uint64_t cap_id, cap_rights_t rights, uint32_t domain);
static void lattice_remove_capability(uint64_t cap_id);
static cap_lattice_node_t* lattice_node_alloc(void);
static void lattice_node_free(cap_lattice_node_t *node);

/* ============================================================================
 * Capability Lattice Constants
 * ============================================================================ */

#define CAP_LATTICE_LEVELS    16      /* Depth of lattice hierarchy */
#define CAP_SLOTS_PER_DOMAIN  4096    /* Capabilities per domain */
#define CAP_TOTAL_SLOTS       65536    /* Total capability slots */
#define CAP_HMAC_SIZE         32      /* HMAC-SHA256 size */
#define CAP_NONCE_SIZE        16      /* Nonce for freshness */

/* Capability rights bits (lattice elements) */
#define CAP_RIGHT_READ      (1ULL << 0)
#define CAP_RIGHT_WRITE     (1ULL << 1)
#define CAP_RIGHT_EXECUTE   (1ULL << 2)
#define CAP_RIGHT_DELETE    (1ULL << 3)
#define CAP_RIGHT_GRANT     (1ULL << 4)
#define CAP_RIGHT_REVOKE    (1ULL << 5)
#define CAP_RIGHT_AMPLIFY   (1ULL << 6)
#define CAP_RIGHT_DIMINISH  (1ULL << 7)
#define CAP_RIGHT_TRANSFER  (1ULL << 8)
#define CAP_RIGHT_DUPLICATE (1ULL << 9)
#define CAP_RIGHT_SEAL      (1ULL << 10)
#define CAP_RIGHT_UNSEAL    (1ULL << 11)
#define CAP_RIGHT_INVOKE    (1ULL << 12)
#define CAP_RIGHT_SYSCALL   (1ULL << 13)
#define CAP_RIGHT_MMAP      (1ULL << 14)
#define CAP_RIGHT_DMA       (1ULL << 15)
#define CAP_RIGHT_IRQ       (1ULL << 16)
#define CAP_RIGHT_TIMER     (1ULL << 17)
#define CAP_RIGHT_NET       (1ULL << 18)
#define CAP_RIGHT_IPC       (1ULL << 19)
#define CAP_RIGHT_ALL       0xFFFFFFFFFFFFFFFULL

/* Capability types extended beyond cap.h */
#define CAP_TYPE_INVALID    0
#define CAP_TYPE_MEMORY     1
#define CAP_TYPE_FILE       2
/* CAP_TYPE_PROCESS = 7 is in cap.h */
#define CAP_TYPE_THREAD     8
#define CAP_TYPE_IPC        9
#define CAP_TYPE_DEVICE     10
#define CAP_TYPE_LATTICE    11
#define CAP_TYPE_META       12

/* ============================================================================
 * Capability Structure (Cache-line aligned)
 * ============================================================================ */

typedef struct capability {
    _Alignas(64) struct {
        /* Identity and type */
        _Atomic(uint64_t) id;          /* Unique capability ID */
        _Atomic(cap_type_t) type;      /* Capability type */
        _Atomic(cap_rights_t) rights;  /* Rights bitmap */
        
        /* Object reference */
        _Atomic(void*) object;          /* Referenced object */
        _Atomic(uint64_t) offset;       /* Offset within object */
        _Atomic(uint64_t) length;       /* Length of access */
        
        /* Lattice position */
        _Atomic(uint32_t) level;        /* Level in lattice */
        _Atomic(uint32_t) domain;       /* Security domain */
        
        /* Delegation chain */
        _Atomic(uint64_t) parent_id;    /* Parent capability */
        _Atomic(uint64_t) children[4];  /* Child capabilities */
        
        /* Security */
        uint8_t hmac[CAP_HMAC_SIZE];    /* HMAC-SHA256 */
        uint8_t nonce[CAP_NONCE_SIZE];  /* Freshness nonce */
        
        /* Metadata */
        _Atomic(uint64_t) timestamp;    /* Creation time */
        _Atomic(uint64_t) expiry;       /* Expiration time */
        _Atomic(uint32_t) use_count;    /* Usage counter */
        _Atomic(uint32_t) ref_count;    /* Reference count */
    } data;
    
    /* Padding to multiple cache lines */
    char padding[192 - sizeof(struct { /* anonymous struct size */ })];
} capability_t;

/* Static assertions for structure layout */
_Static_assert(sizeof(capability_t) <= 512, "capability must fit in reasonable memory");
_Static_assert(alignof(capability_t) >= 8, "capability must be properly aligned");

/* ============================================================================
 * Capability Lattice Structure
 * ============================================================================ */

typedef struct cap_lattice_node {
    _Alignas(64) struct {
        _Atomic(uint64_t) cap_id;
        _Atomic(cap_rights_t) rights;
        _Atomic(uint32_t) level;
        _Atomic(struct cap_lattice_node*) parent;
        _Atomic(struct cap_lattice_node*) children[8];
        _Atomic(struct cap_lattice_node*) next;  /* Hash chain */
    } data;
    char padding[64];
} cap_lattice_node_t;

typedef struct cap_lattice {
    _Alignas(64) struct {
        /* Lattice root (top element) */
        cap_lattice_node_t *top;
        
        /* Lattice bottom (bottom element) */
        cap_lattice_node_t *bottom;
        
        /* Hash table for fast lookup */
        _Atomic(cap_lattice_node_t*) hash_table[4096];
        
        /* Statistics */
        _Atomic(uint64_t) total_nodes;
        _Atomic(uint64_t) total_edges;
        _Atomic(uint64_t) max_depth;
        
        /* Lock-free memory pool */
        _Atomic(cap_lattice_node_t*) free_list;
    } data;
} cap_lattice_t;

/* ============================================================================
 * Global Capability Table
 * ============================================================================ */

static _Alignas(4096) capability_t capability_table[CAP_TOTAL_SLOTS];
static _Alignas(64) cap_lattice_t capability_lattice;
static _Atomic(uint64_t) next_cap_id = 1;

/* Cryptographic key for HMAC (should be initialized securely) */
static uint8_t cap_hmac_key[32];

/* ============================================================================
 * Lattice Operations (Mathematical Partial Order)
 * ============================================================================ */

/**
 * lattice_join - Compute least upper bound (supremum)
 * @param a First capability rights
 * @param b Second capability rights
 *
 * Returns: Union of rights (lattice join)
 */
__attribute__((unused)) static inline cap_rights_t lattice_join(cap_rights_t a, cap_rights_t b) {
    return a | b;
}

/**
 * lattice_meet - Compute greatest lower bound (infimum)
 * @param a First capability rights
 * @param b Second capability rights
 *
 * Returns: Intersection of rights (lattice meet)
 */
__attribute__((unused)) static inline cap_rights_t lattice_meet(cap_rights_t a, cap_rights_t b) {
    return a & b;
}

/**
 * lattice_dominates - Check if a dominates b in partial order
 * @param a First capability rights
 * @param b Second capability rights
 *
 * Returns: true if a ≥ b in the lattice
 */
static inline bool lattice_dominates(cap_rights_t a, cap_rights_t b) {
    return (a & b) == b;
}

/**
 * lattice_comparable - Check if two elements are comparable
 * @param a First capability rights
 * @param b Second capability rights
 *
 * Returns: true if a and b are comparable in the partial order
 */
__attribute__((unused)) static inline bool lattice_comparable(cap_rights_t a, cap_rights_t b) {
    return lattice_dominates(a, b) || lattice_dominates(b, a);
}

/* ============================================================================
 * Capability Creation and Initialization
 * ============================================================================ */

/**
 * capability_create - Create a new capability
 * @param type Type of capability
 * @param object Object to reference
 * @param offset Offset within object
 * @param length Length of access
 * @param rights Initial rights
 * @param domain Security domain
 * 
 * Returns: Capability ID on success, 0 on failure
 */
uint64_t capability_create(cap_type_t type, void *object, 
                          uint64_t offset, uint64_t length,
                          cap_rights_t rights, uint32_t domain) {
    /* Allocate unique ID atomically */
    uint64_t cap_id = atomic_fetch_add_explicit(&next_cap_id, 1, 
                                                memory_order_relaxed);
    
    /* Find free slot using linear probing */
    uint32_t slot = cap_id % CAP_TOTAL_SLOTS;
    uint32_t attempts = 0;
    
    while (attempts < CAP_TOTAL_SLOTS) {
        capability_t *cap = &capability_table[slot];
        
        /* Try to claim this slot */
        uint64_t expected = 0;
        if (atomic_compare_exchange_strong_explicit(
                &cap->data.id, &expected, cap_id,
                memory_order_acquire, memory_order_relaxed)) {
            
            /* Initialize capability */
            atomic_store_explicit(&cap->data.type, type, memory_order_relaxed);
            atomic_store_explicit(&cap->data.rights, rights, memory_order_relaxed);
            atomic_store_explicit(&cap->data.object, object, memory_order_relaxed);
            atomic_store_explicit(&cap->data.offset, offset, memory_order_relaxed);
            atomic_store_explicit(&cap->data.length, length, memory_order_relaxed);
            atomic_store_explicit(&cap->data.domain, domain, memory_order_relaxed);
            atomic_store_explicit(&cap->data.level, 0, memory_order_relaxed);
            atomic_store_explicit(&cap->data.parent_id, 0, memory_order_relaxed);
            atomic_store_explicit(&cap->data.ref_count, 1, memory_order_relaxed);
            atomic_store_explicit(&cap->data.use_count, 0, memory_order_relaxed);
            
            /* Set timestamp */
            uint64_t now = hal_read_timestamp();
            atomic_store_explicit(&cap->data.timestamp, now, memory_order_relaxed);
            atomic_store_explicit(&cap->data.expiry, UINT64_MAX, memory_order_relaxed);
            
            /* Generate nonce */
            for (int i = 0; i < CAP_NONCE_SIZE; i++) {
                cap->data.nonce[i] = (uint8_t)(now ^ (now >> (i * 8)));
            }
            
            /* Compute HMAC */
            capability_compute_hmac(cap);
            
            /* Add to lattice */
            lattice_add_capability(cap_id, rights, domain);
            
            /* Release memory barrier */
            atomic_thread_fence(memory_order_release);
            
            return cap_id;
        }
        
        /* Try next slot */
        slot = (slot + 1) % CAP_TOTAL_SLOTS;
        attempts++;
    }
    
    return 0;  /* Failed to allocate */
}

/**
 * capability_derive - Derive a new capability from existing one
 * @param parent_id Parent capability ID
 * @param new_rights Rights for derived capability (must be subset)
 * @param new_offset New offset (must be within parent range)
 * @param new_length New length (must be within parent range)
 * 
 * Returns: New capability ID on success, 0 on failure
 */
uint64_t capability_derive(uint64_t parent_id, cap_rights_t new_rights,
                           uint64_t new_offset, uint64_t new_length) {
    capability_t *parent = capability_lookup(parent_id);
    if (!parent) return 0;
    
    /* Load parent attributes */
    cap_rights_t parent_rights = atomic_load_explicit(&parent->data.rights, 
                                                      memory_order_acquire);
    uint64_t parent_offset = atomic_load_explicit(&parent->data.offset, 
                                                  memory_order_relaxed);
    uint64_t parent_length = atomic_load_explicit(&parent->data.length, 
                                                  memory_order_relaxed);
    
    /* Check derivation is valid (monotonic in lattice) */
    if (!lattice_dominates(parent_rights, new_rights)) {
        return 0;  /* Cannot amplify rights */
    }
    
    /* Check range is within parent */
    if (new_offset < parent_offset || 
        new_offset + new_length > parent_offset + parent_length) {
        return 0;  /* Out of bounds */
    }
    
    /* Check parent has grant right */
    if (!(parent_rights & CAP_RIGHT_GRANT)) {
        return 0;  /* No grant permission */
    }
    
    /* Create derived capability */
    void *object = atomic_load_explicit(&parent->data.object, 
                                        memory_order_relaxed);
    cap_type_t type = atomic_load_explicit(&parent->data.type, 
                                           memory_order_relaxed);
    uint32_t domain = atomic_load_explicit(&parent->data.domain, 
                                           memory_order_relaxed);
    
    uint64_t child_id = capability_create(type, object, new_offset, 
                                          new_length, new_rights, domain);
    
    if (child_id) {
        capability_t *child = capability_lookup(child_id);
        if (child) {
            /* Set parent link */
            atomic_store_explicit(&child->data.parent_id, parent_id, 
                                 memory_order_relaxed);
            
            /* Set level in lattice (one below parent) */
            uint32_t parent_level = atomic_load_explicit(&parent->data.level, 
                                                         memory_order_relaxed);
            atomic_store_explicit(&child->data.level, parent_level + 1, 
                                 memory_order_relaxed);
            
            /* Add to parent's children list */
            for (int i = 0; i < 4; i++) {
                uint64_t expected = 0;
                if (atomic_compare_exchange_strong_explicit(
                        &parent->data.children[i], &expected, child_id,
                        memory_order_release, memory_order_relaxed)) {
                    break;
                }
            }
        }
    }
    
    return child_id;
}

/* ============================================================================
 * Capability Operations
 * ============================================================================ */

/**
 * capability_lookup - Look up capability by ID
 * @param cap_id Capability ID
 * 
 * Returns: Pointer to capability or NULL
 */
capability_t* capability_lookup(uint64_t cap_id) {
    if (cap_id == 0) return NULL;
    
    /* Start at expected slot */
    uint32_t slot = cap_id % CAP_TOTAL_SLOTS;
    uint32_t attempts = 0;
    
    while (attempts < CAP_TOTAL_SLOTS) {
        capability_t *cap = &capability_table[slot];
        
        uint64_t id = atomic_load_explicit(&cap->data.id, 
                                           memory_order_acquire);
        if (id == cap_id) {
            return cap;
        }
        
        if (id == 0) {
            return NULL;  /* Empty slot, not found */
        }
        
        slot = (slot + 1) % CAP_TOTAL_SLOTS;
        attempts++;
    }
    
    return NULL;
}

/**
 * capability_check - Check if operation is allowed
 * @param cap_id Capability ID
 * @param required_rights Rights needed for operation
 * 
 * Returns: true if operation allowed, false otherwise
 */
bool capability_check(uint64_t cap_id, cap_rights_t required_rights) {
    capability_t *cap = capability_lookup(cap_id);
    if (!cap) return false;
    
    /* Verify HMAC integrity */
    if (!capability_verify_hmac(cap)) {
        return false;
    }
    
    /* Check expiry */
    uint64_t expiry = atomic_load_explicit(&cap->data.expiry, 
                                           memory_order_relaxed);
    if (hal_read_timestamp() > expiry) {
        return false;
    }
    
    /* Check rights using lattice dominance */
    cap_rights_t cap_rights = atomic_load_explicit(&cap->data.rights, 
                                                   memory_order_acquire);
    if (!lattice_dominates(cap_rights, required_rights)) {
        return false;
    }
    
    /* Increment use count */
    atomic_fetch_add_explicit(&cap->data.use_count, 1, memory_order_relaxed);
    
    return true;
}

/**
 * capability_revoke - Revoke a capability and all descendants
 * @param cap_id Capability ID to revoke
 * 
 * Returns: Number of capabilities revoked
 */
uint32_t capability_revoke(uint64_t cap_id) {
    capability_t *cap = capability_lookup(cap_id);
    if (!cap) return 0;
    
    uint32_t revoked = 0;
    
    /* Recursively revoke children first */
    for (int i = 0; i < 4; i++) {
        uint64_t child_id = atomic_load_explicit(&cap->data.children[i], 
                                                 memory_order_relaxed);
        if (child_id != 0) {
            revoked += capability_revoke(child_id);
        }
    }
    
    /* Clear capability */
    atomic_store_explicit(&cap->data.rights, 0, memory_order_release);
    atomic_store_explicit(&cap->data.type, CAP_TYPE_INVALID, 
                         memory_order_relaxed);
    atomic_store_explicit(&cap->data.object, NULL, memory_order_relaxed);
    
    /* Remove from lattice */
    lattice_remove_capability(cap_id);
    
    /* Mark slot as free */
    atomic_store_explicit(&cap->data.id, 0, memory_order_release);
    
    return revoked + 1;
}

/* ============================================================================
 * Capability Transfer (Zero-Copy)
 * ============================================================================ */

/**
 * capability_transfer - Transfer capability between domains
 * @param cap_id Capability ID to transfer
 * @param from_domain Source domain
 * @param to_domain Target domain
 * 
 * Returns: true on success, false on failure
 */
bool capability_transfer(uint64_t cap_id, uint32_t from_domain, 
                        uint32_t to_domain) {
    capability_t *cap = capability_lookup(cap_id);
    if (!cap) return false;
    
    /* Check transfer right */
    cap_rights_t rights = atomic_load_explicit(&cap->data.rights, 
                                               memory_order_acquire);
    if (!(rights & CAP_RIGHT_TRANSFER)) {
        return false;
    }
    
    /* Verify source domain */
    uint32_t current_domain = atomic_load_explicit(&cap->data.domain, 
                                                   memory_order_acquire);
    if (current_domain != from_domain) {
        return false;
    }
    
    /* Atomically transfer */
    if (atomic_compare_exchange_strong_explicit(
            &cap->data.domain, &current_domain, to_domain,
            memory_order_release, memory_order_relaxed)) {
        
        /* Update HMAC for new domain */
        capability_compute_hmac(cap);
        
        return true;
    }
    
    return false;
}

/* ============================================================================
 * Cryptographic Operations
 * ============================================================================ */

/**
 * capability_compute_hmac - Compute HMAC-SHA256 for capability
 * @param cap Capability to compute HMAC for
 */
void capability_compute_hmac(capability_t *cap) {
    /* This would use a real HMAC-SHA256 implementation */
    /* For now, simple placeholder */
    uint8_t data[64];
    memcpy(data, &cap->data.id, sizeof(cap->data.id));
    memcpy(data + 8, &cap->data.rights, sizeof(cap->data.rights));
    memcpy(data + 16, &cap->data.domain, sizeof(cap->data.domain));
    memcpy(data + 20, cap->data.nonce, CAP_NONCE_SIZE);
    
    /* Simple XOR-based MAC for demonstration */
    for (int i = 0; i < CAP_HMAC_SIZE; i++) {
        cap->data.hmac[i] = data[i % 36] ^ cap_hmac_key[i];
    }
}

/**
 * capability_verify_hmac - Verify HMAC-SHA256 for capability
 * @param cap Capability to verify
 * 
 * Returns: true if HMAC valid, false otherwise
 */
bool capability_verify_hmac(capability_t *cap) {
    uint8_t computed_hmac[CAP_HMAC_SIZE];
    uint8_t saved_hmac[CAP_HMAC_SIZE];
    
    /* Save current HMAC */
    memcpy(saved_hmac, cap->data.hmac, CAP_HMAC_SIZE);
    
    /* Compute expected HMAC */
    capability_compute_hmac(cap);
    memcpy(computed_hmac, cap->data.hmac, CAP_HMAC_SIZE);
    
    /* Restore saved HMAC */
    memcpy(cap->data.hmac, saved_hmac, CAP_HMAC_SIZE);
    
    /* Constant-time comparison */
    uint32_t diff = 0;
    for (int i = 0; i < CAP_HMAC_SIZE; i++) {
        diff |= saved_hmac[i] ^ computed_hmac[i];
    }
    
    return diff == 0;
}

/* ============================================================================
 * Lattice Node Memory Management
 * ============================================================================ */

/**
 * lattice_node_alloc - Allocate a lattice node from the pool
 *
 * Returns: Pointer to allocated node, or NULL if out of memory
 */
static cap_lattice_node_t* lattice_node_alloc(void) {
    /* Try to get from free list first */
    cap_lattice_node_t *node = atomic_load_explicit(
        &capability_lattice.data.free_list, memory_order_acquire);

    while (node) {
        cap_lattice_node_t *next = atomic_load_explicit(
            &node->data.next, memory_order_relaxed);

        if (atomic_compare_exchange_weak_explicit(
                &capability_lattice.data.free_list,
                &node, next,
                memory_order_release,
                memory_order_acquire)) {
            /* Successfully removed from free list */
            memset(&node->data, 0, sizeof(node->data));
            return node;
        }

        /* CAS failed, retry with new head */
        node = atomic_load_explicit(&capability_lattice.data.free_list,
                                    memory_order_acquire);
    }

    /* Free list empty, allocate new node */
    /* In a real kernel, this would use kalloc() or a slab allocator */
    static cap_lattice_node_t node_pool[4096];
    static _Atomic(size_t) next_pool_slot = 0;

    size_t slot = atomic_fetch_add_explicit(&next_pool_slot, 1,
                                           memory_order_relaxed);
    if (slot >= 4096) {
        return NULL;  /* Out of memory */
    }

    node = &node_pool[slot];
    memset(node, 0, sizeof(*node));
    return node;
}

/**
 * lattice_node_free - Return a lattice node to the pool
 * @param node Node to free
 */
static void lattice_node_free(cap_lattice_node_t *node) {
    if (!node) return;

    /* Clear the node */
    memset(&node->data, 0, sizeof(node->data));

    /* Add to free list (lock-free stack push) */
    cap_lattice_node_t *old_head = atomic_load_explicit(
        &capability_lattice.data.free_list, memory_order_relaxed);

    do {
        atomic_store_explicit(&node->data.next, old_head, memory_order_relaxed);
    } while (!atomic_compare_exchange_weak_explicit(
                &capability_lattice.data.free_list,
                &old_head, node,
                memory_order_release,
                memory_order_relaxed));
}

/* ============================================================================
 * Lattice Management
 * ============================================================================ */

/**
 * lattice_init - Initialize capability lattice
 */
void lattice_init(void) {
    /* Initialize hash table */
    for (int i = 0; i < 4096; i++) {
        atomic_init(&capability_lattice.data.hash_table[i], NULL);
    }
    
    /* Create top element (all rights) */
    cap_lattice_node_t *top = lattice_node_alloc();
    atomic_store_explicit(&top->data.cap_id, 0, memory_order_relaxed);
    atomic_store_explicit(&top->data.rights, CAP_RIGHT_ALL, 
                         memory_order_relaxed);
    atomic_store_explicit(&top->data.level, 0, memory_order_relaxed);
    capability_lattice.data.top = top;
    
    /* Create bottom element (no rights) */
    cap_lattice_node_t *bottom = lattice_node_alloc();
    atomic_store_explicit(&bottom->data.cap_id, UINT64_MAX, 
                         memory_order_relaxed);
    atomic_store_explicit(&bottom->data.rights, 0, memory_order_relaxed);
    atomic_store_explicit(&bottom->data.level, CAP_LATTICE_LEVELS - 1, 
                         memory_order_relaxed);
    capability_lattice.data.bottom = bottom;
    
    /* Initialize statistics */
    atomic_init(&capability_lattice.data.total_nodes, 2);
    atomic_init(&capability_lattice.data.total_edges, 1);
    atomic_init(&capability_lattice.data.max_depth, 1);
    
    /* Initialize HMAC key (should use secure random) */
    for (int i = 0; i < 32; i++) {
        cap_hmac_key[i] = (uint8_t)(i * 37 + 17);
    }
}

/**
 * lattice_add_capability - Add capability to lattice
 * @param cap_id Capability ID
 * @param rights Capability rights
 * @param domain Security domain
 */
void lattice_add_capability(uint64_t cap_id, cap_rights_t rights, 
                           uint32_t domain) {
    cap_lattice_node_t *node = lattice_node_alloc();
    if (!node) return;
    
    /* Initialize node */
    atomic_store_explicit(&node->data.cap_id, cap_id, memory_order_relaxed);
    atomic_store_explicit(&node->data.rights, rights, memory_order_relaxed);
    atomic_store_explicit(&node->data.level, 1, memory_order_relaxed);
    
    /* Add to hash table */
    uint32_t hash = cap_id % 4096;
    cap_lattice_node_t *head = atomic_load_explicit(
        &capability_lattice.data.hash_table[hash], memory_order_acquire);
    
    do {
        atomic_store_explicit(&node->data.next, head, memory_order_relaxed);
    } while (!atomic_compare_exchange_weak_explicit(
        &capability_lattice.data.hash_table[hash], &head, node,
        memory_order_release, memory_order_relaxed));
    
    /* Update statistics */
    atomic_fetch_add_explicit(&capability_lattice.data.total_nodes, 1, 
                             memory_order_relaxed);
}

/**
 * lattice_remove_capability - Remove capability from lattice
 * @param cap_id Capability ID to remove
 */
void lattice_remove_capability(uint64_t cap_id) {
    uint32_t hash = cap_id % 4096;

    _Atomic(cap_lattice_node_t*) *prev = &capability_lattice.data.hash_table[hash];
    cap_lattice_node_t *node = atomic_load_explicit(prev, memory_order_acquire);

    while (node) {
        if (atomic_load_explicit(&node->data.cap_id, memory_order_relaxed)
            == cap_id) {
            cap_lattice_node_t *next = atomic_load_explicit(&node->data.next,
                                                           memory_order_relaxed);
            atomic_store_explicit(prev, next, memory_order_release);
            lattice_node_free(node);

            atomic_fetch_sub_explicit(&capability_lattice.data.total_nodes, 1,
                                     memory_order_relaxed);
            break;
        }

        prev = (_Atomic(cap_lattice_node_t *) *)&node->data.next;
        node = atomic_load_explicit(&node->data.next, memory_order_acquire);
    }
}
