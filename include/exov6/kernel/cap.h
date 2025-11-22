/**
 * @file cap.h
 * @brief Public capability table ABI (minimal, stable layout).
 *
 * This header exposes the minimal capability entry layout used by
 * external tools and tests. It intentionally avoids pulling in
 * kernel-internal headers. Keep this structure small and stable.
 */
#pragma once

#include <stdint.h>

/** Opaque capability identifier type. */
typedef uint64_t cap_id_t;

/** Maximum number of capabilities in the system */
#define CAP_MAX 65536

/**
 * @brief Capability type discriminator.
 */
enum cap_type {
  CAP_TYPE_NONE = 0,
  CAP_TYPE_PAGE = 1,
  CAP_TYPE_IOPORT = 2,
  CAP_TYPE_IRQ = 3,
  CAP_TYPE_DMA = 4,
  CAP_TYPE_HYPERVISOR = 5,
  CAP_TYPE_CRYPTOKEY = 6,
  CAP_TYPE_PROCESS = 7
};

/**
 * @brief Public capability entry as observed by userland/tools.
 *
 * Layout is part of the public ABI; do not change without bumping
 * tests and all consumers. Expected size is 20 bytes, alignment 4.
 */
struct cap_entry {
  uint16_t type;     /**< Capability type. */
  uint16_t refcnt;   /**< Reference count (truncated view). */
  uint16_t epoch;    /**< Epoch (upper 16 bits of `cap_id_t`). */
  uint32_t resource; /**< Resource identifier (implementation-defined). */
  uint32_t rights;   /**< Rights bitmask. */
  uint32_t owner;    /**< Owning zone/process identifier. */
};

#ifdef __cplusplus
static_assert(sizeof(struct cap_entry) == 20, "ABI mismatch: cap_entry size");
static_assert(alignof(struct cap_entry) == 4, "ABI mismatch: cap_entry align");
#else
_Static_assert(sizeof(struct cap_entry) == 20, "ABI mismatch: cap_entry size");
_Static_assert(_Alignof(struct cap_entry) == 4, "ABI mismatch: cap_entry align");
#endif

/** Global epoch (upper 16 bits embedded in identifiers). */
extern uint32_t global_epoch;

/** True once the capability table is initialized. */
extern int cap_table_ready;

/** Initialize the capability table. */
void cap_table_init(void);

/**
 * @brief Allocate a new capability entry.
 * @param type Capability type discriminator.
 * @param resource Implementation-defined resource id.
 * @param rights Rights bitmask.
 * @param owner Owning zone/process id.
 * @return Non-zero capability id on success, 0 on failure.
 */
cap_id_t cap_table_alloc(uint16_t type, uint32_t resource, uint32_t rights,
                         uint32_t owner);

/**
 * @brief Look up a capability by id into a user-provided buffer.
 * @param id Capability identifier.
 * @param out Destination buffer for the entry.
 * @return 0 on success, negative on failure.
 */
int cap_table_lookup(cap_id_t id, struct cap_entry *out);

/** Increase the reference count of a capability. */
void cap_table_inc(cap_id_t id);

/** Decrease the reference count of a capability. */
void cap_table_dec(cap_id_t id);

/**
 * @brief Revoke a capability.
 * Increments the embedded epoch and frees the slot.
 * @return 0 on success, negative on failure.
 */
int cap_table_remove(cap_id_t id);

/** Convenience alias for revoke semantics. */
int cap_revoke(cap_id_t id);

/**
 * @brief Capability validation result codes
 */
typedef enum {
    VALIDATION_SUCCESS = 0,      /**< Capability is valid */
    VALIDATION_INVALID_ID = 1,   /**< Invalid capability ID */
    VALIDATION_REVOKED = 2,      /**< Capability has been revoked */
    VALIDATION_TYPE_MISMATCH = 3,/**< Capability type mismatch */
    VALIDATION_INSUFFICIENT_RIGHTS = 4, /**< Insufficient rights */
    VALIDATION_OWNER_MISMATCH = 5,/**< Owner mismatch */
    VALIDATION_EXPIRED = 6       /**< Capability has expired */
} cap_validation_result_t;

/**
 * @brief Validate a capability and retrieve its entry
 * @param id Capability identifier
 * @param out_entry_if_valid Destination for entry if valid (can be NULL)
 * @return Validation result code
 */
cap_validation_result_t cap_validate_unified(cap_id_t id, struct cap_entry *out_entry_if_valid);
