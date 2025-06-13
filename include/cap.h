#pragma once

#include <stdint.h>
#include <stdatomic.h> // For _Atomic
#include "include/octonion.h"
#include "include/lattice_types.h"
#include "include/dag.h" // For struct dag_node
#include "types.h" // For cap_type enum if still used directly

typedef enum cap_type cap_type_t;
typedef uint64_t cap_id_t; // Matches usage in the provided cap_table.c

struct cap_entry {
    // === Epoch-based fields ===
    uint64_t epoch;
    uint64_t generation; // For sub-epoch versioning if used by epoch logic
    cap_id_t id;

    // === DAG enforcement ===
    struct dag_node *access_path_ptr;

    // === Quantum-safe auth (Union as suggested) ===
    union {
        octonion_t auth_token;          // Internal fast auth
        lattice_sig_t lattice_auth_signature; // External/persistent auth
    } auth;

    // === Resource identification (Lattice based) ===
    lattice_pt resource_identifier_lattice;

    // === Standard fields ===
    cap_type_t type;
    uint64_t rights_mask;
    void *resource_ptr; // Generic pointer to the actual resource

    // === Metadata/flags (incorporating user feedback) ===
    struct {
        uint32_t dag_verified : 1;
        uint32_t crypto_verified : 1; // General crypto flag
        uint32_t epoch_valid : 1;
        uint32_t quantum_safe : 1;  // Indicates if lattice_auth_signature is used
        // uint32_t numa_hint : 8; // Can be added later if needed
        uint32_t reserved : 28; // Adjust reserved bits
    } flags;

    // === Kernel internal management fields ===
    _Atomic uint16_t refcnt; // Made atomic based on provided cap_table.c
    uint32_t owner;
};

// Comment out sizeof assert for now, will verify after compilation
// _Static_assert(sizeof(struct cap_entry) == YYY, "ABI mismatch: cap_entry size");
_Static_assert(_Alignof(struct cap_entry) >= 8, "struct cap_entry alignment incorrect (expected >= 8)");

extern uint64_t global_current_epoch; // Changed from uint32_t based on provided cap_table.c
extern int cap_table_ready;

void cap_table_init(void);

cap_id_t cap_table_alloc(
    cap_type_t type,
    void* resource_ptr,
    uint64_t rights,
    uint32_t owner, // Added owner
    struct dag_node* access_path_ptr,
    const lattice_pt* resource_lattice_id_param, // For initializing resource_identifier_lattice
    int is_quantum_safe // To set the quantum_safe flag and decide which auth to init
);

int cap_table_lookup(cap_id_t id, struct cap_entry *out);
void cap_table_inc_ref(cap_id_t id);
void cap_table_dec_ref(cap_id_t id);
int cap_revoke(cap_id_t id);

typedef enum {
    VALIDATION_SUCCESS,
    VALIDATION_FAILED_NULL, // Entry not found or null
    VALIDATION_FAILED_EPOCH,
    VALIDATION_FAILED_DAG,
    VALIDATION_FAILED_CRYPTO_AUTH // Generic crypto failure for now
} cap_validation_result_t;

cap_validation_result_t cap_validate_unified(cap_id_t id, struct cap_entry *out_entry_if_valid);

// Ensure this is the end of the file if it was guarded by #ifndef CAP_H ... #endif
// Since #pragma once is used, this is less critical but good for consistency if migrating from old style.
// #endif // CAP_H typically matches a #ifndef CAP_H at the top.
// With #pragma once, an explicit #endif is not strictly necessary for the guard itself.
