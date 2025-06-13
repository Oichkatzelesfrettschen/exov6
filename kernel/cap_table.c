#include "include/cap.h"      // For new struct cap_entry, cap_id_t, etc.
#include "include/types.h"    // For basic types if not covered by stdint.h
#include "include/defs.h"     // For kalloc, kfree, panic (if used)
#include "engine/kernel/spinlock.h" // For struct spinlock, initlock, acquire, release
#include "include/octonion.h" // For octonion_t and operations
#include "include/lattice_types.h" // For lattice_pt, lattice_sig_t
#include "include/dag.h"      // For struct dag_node (definition for stubs)
#include <string.h>           // For memset, memcpy, memcmp
#include <stdint.h>           // For UINT64_MAX, standard integer types
#include <stdatomic.h>        // For atomic operations like atomic_store, atomic_fetch_add

// --- Globals ---
static struct spinlock cap_lock;
static struct cap_entry cap_table[CAP_MAX]; // Array of the new unified cap_entry
uint64_t global_current_epoch = 1; // Start global epoch at 1 (0 might mean uninitialized)
int cap_table_ready = 0; // Indicates if the capability table is initialized

// --- System Key Stub for Octonion Auth ---
// This would be a securely managed key in a real system.
static const octonion_t SYSTEM_OCTONION_KEY_STUB = {
    0.123, 0.456, 0.789, 0.101, 0.112, 0.131, 0.415, 0.161
};

// --- Forward declarations for static helper functions ---
static uint16_t get_index_from_id(cap_id_t id);
static uint64_t get_epoch_from_id(cap_id_t id);
static cap_id_t generate_cap_id(uint16_t index, uint64_t epoch);

// Stub function implementations
static void generate_stub_auth_token(const struct cap_entry* entry, octonion_t* out_token) {
    // Simplified generation logic for the stub.
    // A real implementation would use cryptographic hashing or HMAC with the system key.
    // For this stub, combine some fields and "mix" with the system key.
    if (!entry || !out_token) return;
    octonion_t temp_data = {
        (double)entry->id + 0.1, (double)entry->epoch + 0.2, (double)entry->type + 0.3, (double)entry->rights_mask + 0.4,
        (double)(uintptr_t)entry->resource_ptr + 0.5, (double)(uintptr_t)entry->access_path_ptr + 0.6,
        (double)entry->owner + 0.7, (double)entry->generation + 0.8
    };
    // Keep using quaternion_multiply as the stub mixing function for now
    *out_token = quaternion_multiply(temp_data, SYSTEM_OCTONION_KEY_STUB);
    // Add another mix step for pseudo-complexity
    octonion_t key_squared = quaternion_multiply(SYSTEM_OCTONION_KEY_STUB, SYSTEM_OCTONION_KEY_STUB);
    *out_token = quaternion_multiply(*out_token, key_squared);
}

static int verify_stub_auth_token(const struct cap_entry* entry, const octonion_t* token_to_check) {
    if (!entry || !token_to_check) return 0;
    octonion_t expected_token;
    generate_stub_auth_token(entry, &expected_token); // Regenerate the token
    return octonion_equals(token_to_check, &expected_token); // New way
}

static void generate_lattice_signature_stub(const struct cap_entry* entry, lattice_sig_t* out_sig) {
    if (!entry || !out_sig) return;
    // Simple "hash" of some capability fields
    uint8_t digest[8]; // Use 8 bytes of the signature for this digest
    memset(digest, 0, sizeof(digest));
    digest[0] = (uint8_t)(entry->id & 0xFF);
    digest[1] = (uint8_t)((entry->id >> 8) & 0xFF);
    digest[2] = (uint8_t)(entry->epoch & 0xFF);
    digest[3] = (uint8_t)(entry->type & 0xFF);
    digest[4] = (uint8_t)(entry->rights_mask & 0xFF);
    digest[5] = (uint8_t)(entry->owner & 0xFF);
    digest[6] = (uint8_t)((uintptr_t)entry->resource_ptr & 0xFF);
    digest[7] = (uint8_t)((uintptr_t)entry->access_path_ptr & 0xFF);

    // Fill sig_data: first part is digest, rest is a pattern
    memset(out_sig->sig_data, 0xCC, sizeof(out_sig->sig_data)); // Default pattern
    memcpy(out_sig->sig_data, digest, sizeof(digest));          // Embed digest
    out_sig->sig_size = sizeof(out_sig->sig_data); // LATTICE_SIG_BYTES
}

static int verify_lattice_signature_stub(const struct cap_entry* entry, const lattice_sig_t* sig_to_check) {
    if (!entry || !sig_to_check || sig_to_check->sig_size != sizeof(sig_to_check->sig_data)) return 0;

    uint8_t expected_digest[8];
    memset(expected_digest, 0, sizeof(expected_digest));
    expected_digest[0] = (uint8_t)(entry->id & 0xFF);
    expected_digest[1] = (uint8_t)((entry->id >> 8) & 0xFF);
    expected_digest[2] = (uint8_t)(entry->epoch & 0xFF);
    expected_digest[3] = (uint8_t)(entry->type & 0xFF);
    expected_digest[4] = (uint8_t)(entry->rights_mask & 0xFF);
    expected_digest[5] = (uint8_t)(entry->owner & 0xFF);
    expected_digest[6] = (uint8_t)((uintptr_t)entry->resource_ptr & 0xFF);
    expected_digest[7] = (uint8_t)((uintptr_t)entry->access_path_ptr & 0xFF);

    if (memcmp(sig_to_check->sig_data, expected_digest, sizeof(expected_digest)) != 0) {
        return 0; // Digest mismatch
    }

    // Check the rest of the pattern
    for (size_t i = sizeof(expected_digest); i < sig_to_check->sig_size; ++i) {
        if (sig_to_check->sig_data[i] != 0xCC) return 0; // Pattern mismatch
    }
    return 1;
}

// Forward declaration for the recursive helper if needed, or make it static within the main function.
// static int dfs_cycle_check(struct dag_node* current_node, /* potrzebne struktury danych do śledzenia ścieżki/odwiedzonych */);

static int verify_dag_acyclic_stub(struct dag_node* start_node) {
    if (start_node == NULL) {
        return 1; // No path or node to check is considered acyclic.
    }

    // TODO: Implement actual DFS-based cycle detection.
    // This placeholder outlines the conceptual steps. A real implementation
    // would require:
    // 1. A way to mark nodes during traversal (e.g., visiting, visited states).
    //    This might involve adding fields to struct dag_node or using external tracking
    //    if node modification is not possible/desirable here.
    // 2. A starting point for traversal if checking a global graph property,
    //    or if 'start_node' is the entry point for a specific path to validate.

    // Conceptual DFS:
    // Pseudo-code for a recursive DFS helper:
    // int dfs_helper(node, path_set, visited_set):
    //   add node to path_set
    //   add node to visited_set
    //
    //   for each child in node->children:
    //     if child in path_set:
    //       return DETECTED_CYCLE // Cycle detected
    //     if child not in visited_set:
    //       if dfs_helper(child, path_set, visited_set) == DETECTED_CYCLE:
    //         return DETECTED_CYCLE
    //
    //   remove node from path_set
    //   return NO_CYCLE

    // To make it slightly more than a simple 'return 1':
    // Let's simulate a very shallow check: a self-loop on the start_node via its direct children.
    // This requires knowing the structure of dag_node, specifically how children are accessed.
    // Assuming struct dag_node has a field like 'struct dag_node_list* children;'
    // where dag_node_list is 'struct dag_node_list { struct dag_node* node; struct dag_node_list* next; };'
    if (start_node->children) { // Assuming 'children' is a pointer to the head of a list of child nodes
        struct dag_node_list* child_item = start_node->children;
        while (child_item) {
            if (child_item->node == start_node) {
                // Direct self-loop detected
                return 0;
            }
            child_item = child_item->next;
        }
    }

    return 1; // Placeholder: Assume acyclic for now for other cases.
}


// --- Capability Table Management Functions ---

void cap_table_init(void) {
    initlock(&cap_lock, "captbl");
    memset(cap_table, 0, sizeof(cap_table)); // Zero out all entries
    global_current_epoch = 1; // Reset epoch
    cap_table_ready = 1;
}

cap_id_t cap_table_alloc(
    cap_type_t type,
    void* resource_ptr,
    uint64_t rights,
    uint32_t owner,
    struct dag_node* access_path_ptr,
    const lattice_pt* resource_lattice_id_param,
    int is_quantum_safe
) {
    if (!cap_table_ready) {
        // Or panic, depending on system design
        return 0; // Table not initialized
    }
    if (type == CAP_TYPE_NONE) { // Cannot allocate a "NONE" type
        return 0;
    }

    acquire(&cap_lock);
    for (uint16_t i = 1; i < CAP_MAX; i++) { // Index 0 is typically reserved
        if (cap_table[i].type == CAP_TYPE_NONE) { // Found a free slot
            struct cap_entry *entry = &cap_table[i];

            // Initialize Epoch-based fields
            entry->epoch = global_current_epoch;
            entry->generation = 0; // Initial generation
            entry->id = generate_cap_id(i, entry->epoch);

            // Initialize Core capability fields
            entry->type = type;
            entry->resource_ptr = resource_ptr;
            entry->rights_mask = rights;
            entry->owner = owner;

            // Initialize DAG/Lattice fields
            entry->access_path_ptr = access_path_ptr;
            if (resource_lattice_id_param) {
                // Shallow copy for the lattice_pt struct.
                // If lattice_pt.data points to heap memory that cap_entry should own,
                // then a deep copy (allocate and copy content) would be needed here.
                // For now, assume resource_lattice_id_param->data is managed elsewhere or simple.
                entry->resource_identifier_lattice = *resource_lattice_id_param;
            } else {
                memset(&entry->resource_identifier_lattice, 0, sizeof(lattice_pt));
            }

            // Initialize Quantum-safe auth
            if (is_quantum_safe) {
                generate_lattice_signature_stub(entry, &entry->auth.lattice_auth_signature);
            } else {
                generate_stub_auth_token(entry, &entry->auth.auth_token);
            }

            // Initialize Metadata/flags
            entry->flags.dag_verified = 0;    // Verification happens on demand
            entry->flags.crypto_verified = 0; // Verification happens on demand
            entry->flags.epoch_valid = 1;     // Valid upon allocation
            entry->flags.quantum_safe = is_quantum_safe ? 1 : 0;
            entry->flags.reserved = 0;

            // Initialize Kernel internal management fields
            atomic_store(&entry->refcnt, 1);

            release(&cap_lock);
            return entry->id;
        }
    }
    release(&cap_lock);
    return 0; // No free slot found
}

int cap_table_lookup(cap_id_t id, struct cap_entry *out) {
    if (!cap_table_ready || id == 0) return -1;

    uint16_t index = get_index_from_id(id);
    uint64_t epoch_from_id = get_epoch_from_id(id);

    if (index == 0 || index >= CAP_MAX) return -1; // Invalid index

    // No lock needed for initial check if type is NONE, but epoch check needs lock
    // acquire(&cap_lock); // Moved lock acquisition to after index check
    // if (cap_table[index].type == CAP_TYPE_NONE) { // Quick check before lock
    //     release(&cap_lock);
    //     return -1;
    // }
    acquire(&cap_lock);

    struct cap_entry *entry = &cap_table[index];

    if (entry->type == CAP_TYPE_NONE || entry->epoch != epoch_from_id) {
        release(&cap_lock);
        return -1; // Slot is free or epoch mismatch (revoked or reused)
    }

    if (out) {
        *out = *entry; // Copy out the capability entry
    }
    release(&cap_lock);
    return 0; // Success
}

void cap_table_inc_ref(cap_id_t id) {
    if (!cap_table_ready || id == 0) return;

    uint16_t index = get_index_from_id(id);
    uint64_t epoch_from_id = get_epoch_from_id(id);

    if (index == 0 || index >= CAP_MAX) return;

    acquire(&cap_lock);
    struct cap_entry *entry = &cap_table[index];
    if (entry->type != CAP_TYPE_NONE && entry->epoch == epoch_from_id) {
        atomic_fetch_add(&entry->refcnt, 1);
    }
    release(&cap_lock);
}

void cap_table_dec_ref(cap_id_t id) {
    if (!cap_table_ready || id == 0) return;

    uint16_t index = get_index_from_id(id);
    uint64_t epoch_from_id = get_epoch_from_id(id);

    if (index == 0 || index >= CAP_MAX) return;

    acquire(&cap_lock);
    struct cap_entry *entry = &cap_table[index];
    if (entry->type != CAP_TYPE_NONE && entry->epoch == epoch_from_id) {
        if (atomic_fetch_sub(&entry->refcnt, 1) - 1 == 0) {
            // Ref count dropped to zero, effectively "freeing" the slot for reuse.
            // Actual memory for pointed-to data (resource_ptr, access_path_ptr,
            // resource_identifier_lattice.data if deep-copied) should be managed
            // by the subsystem that owns those resources, often before calling dec_ref.
            // This function just marks the cap_entry slot as available.

            // Stub: "Clear" fields to prevent accidental use of stale data
            entry->type = CAP_TYPE_NONE; // Mark as free
            entry->resource_ptr = NULL;
            entry->access_path_ptr = NULL;
            memset(&entry->resource_identifier_lattice, 0, sizeof(lattice_pt));
            memset(&entry->auth, 0, sizeof(entry->auth)); // Zero out auth union
            memset(&entry->flags, 0, sizeof(entry->flags));
            entry->owner = 0;
            entry->rights_mask = 0;
            // Epoch and ID remain for debugging/tracing until slot is overwritten by alloc
        }
    }
    release(&cap_lock);
}

int cap_revoke(cap_id_t id) {
    if (!cap_table_ready || id == 0) return -1;

    uint16_t index = get_index_from_id(id);
    uint64_t epoch_from_id = get_epoch_from_id(id);

    if (index == 0 || index >= CAP_MAX) return -1;

    acquire(&cap_lock);
    struct cap_entry *entry = &cap_table[index];

    if (entry->type == CAP_TYPE_NONE || entry->epoch != epoch_from_id) {
        release(&cap_lock);
        return -1; // Not found or already revoked
    }

    if (entry->epoch == UINT64_MAX) {
        // Epoch is maxed out, cannot increment further.
        // This is a critical condition if the system relies on epoch increment for security.
        // Depending on policy, could panic or mark as permanently unusable.
        // For now, just fail the revocation.
        release(&cap_lock);
        // Consider logging this event: panic("cap_revoke: epoch overflow");
        return -2; // Indicate epoch overflow
    }

    entry->epoch++; // Increment epoch, invalidating old IDs
    // Update global_current_epoch if this new epoch is higher
    if (global_current_epoch <= entry->epoch) {
        global_current_epoch = entry->epoch + 1;
        // Handle wrap-around for global_current_epoch too, though less critical than entry's epoch
        if (global_current_epoch == 0) global_current_epoch = 1;
    }

    // "Free" the slot by marking it as type NONE and clearing sensitive fields.
    // Similar to dec_ref when refcnt hits zero.
    entry->type = CAP_TYPE_NONE;
    atomic_store(&entry->refcnt, 0); // No more valid references
    entry->resource_ptr = NULL;
    entry->access_path_ptr = NULL;
    memset(&entry->resource_identifier_lattice, 0, sizeof(lattice_pt));
    memset(&entry->auth, 0, sizeof(entry->auth));
    memset(&entry->flags, 0, sizeof(entry->flags));
    entry->owner = 0;
    entry->rights_mask = 0;
    // ID field is not cleared, epoch field now holds the new (incremented) epoch.

    release(&cap_lock);
    return 0; // Success
}

cap_validation_result_t cap_validate_unified(cap_id_t id, struct cap_entry *out_entry_if_valid) {
    if (!cap_table_ready) return VALIDATION_FAILED_NULL;

    struct cap_entry current_cap_data; // Local copy to work with after releasing lock

    uint16_t index = get_index_from_id(id);
    uint64_t epoch_from_id = get_epoch_from_id(id);

    if (index == 0 || index >= CAP_MAX) return VALIDATION_FAILED_NULL;

    acquire(&cap_lock);
    struct cap_entry *entry_in_table = &cap_table[index];

    if (entry_in_table->type == CAP_TYPE_NONE) {
        release(&cap_lock);
        return VALIDATION_FAILED_NULL;
    }

    // Epoch Check (Critical: do this while holding the lock)
    if (entry_in_table->epoch != epoch_from_id) {
        release(&cap_lock);
        return VALIDATION_FAILED_EPOCH;
    }
    entry_in_table->flags.epoch_valid = 1; // Mark as checked for this instance

    // Copy to local struct to minimize time holding lock for further checks
    current_cap_data = *entry_in_table;
    release(&cap_lock);

    // DAG Check (can be done on local copy if DAG structure is stable or also copied)
    // Assuming verify_dag_acyclic_stub can work on potentially stale data or is very fast.
    // If DAG structure can change and needs locked access, this must be re-evaluated.
    if (current_cap_data.access_path_ptr && !current_cap_data.flags.dag_verified) {
        if (!verify_dag_acyclic_stub(current_cap_data.access_path_ptr)) {
            // Note: We are not updating flags in the actual table entry here
            // as we've released the lock. Caching flags should be done under lock.
            // This validation function is more of a check than a state update for flags.
            return VALIDATION_FAILED_DAG;
        }
        // current_cap_data.flags.dag_verified = 1; // Reflects check on local copy
    }

    // Crypto Check (on local copy)
    if (!current_cap_data.flags.crypto_verified) {
        if (current_cap_data.flags.quantum_safe) {
            if (!verify_lattice_signature_stub(&current_cap_data, &current_cap_data.auth.lattice_auth_signature)) {
                return VALIDATION_FAILED_CRYPTO_AUTH;
            }
        } else {
            if (!verify_stub_auth_token(&current_cap_data, &current_cap_data.auth.auth_token)) {
                return VALIDATION_FAILED_CRYPTO_AUTH;
            }
        }
        // current_cap_data.flags.crypto_verified = 1; // Reflects check on local copy
    }

    // If all checks passed:
    if (out_entry_if_valid) {
        *out_entry_if_valid = current_cap_data; // Provide the validated (copied) entry
    }
    return VALIDATION_SUCCESS;
}


// --- Static Helper Function Implementations ---

static uint16_t get_index_from_id(cap_id_t id) {
    return (uint16_t)(id & 0xFFFF); // Lower 16 bits for index
}

static uint64_t get_epoch_from_id(cap_id_t id) {
    // Upper bits for epoch. Shift by 16.
    return (id >> 16);
}

static cap_id_t generate_cap_id(uint16_t index, uint64_t epoch) {
    // Combine epoch and index to form a unique ID.
    // Ensure index is within valid range (e.g., < CAP_MAX and not 0).
    // Ensure epoch doesn't overflow into index bits if shifting is different.
    return (epoch << 16) | index;
}
