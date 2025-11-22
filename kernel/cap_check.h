#pragma once
#include "exo.h"
#include "types.h"

/*
 * Capability Validation API
 * Centralized boundary checks for all capability usage.
 *
 * This API enforces the invariants defined in kernel/invariants.md.
 */

/**
 * @brief Check if a capability is valid and has specific rights.
 *
 * Verifies:
 * 1. Capability ID is valid (not EXO_CAP_INVALID)
 * 2. Capability possesses the required rights
 * 3. Capability is owned by the current process
 *
 * @param cap The capability to check
 * @param required_rights Bitmask of rights required (e.g. EXO_CAP_READ)
 * @return 0 on success, -1 on failure
 */
int cap_check(exo_cap cap, uint32_t required_rights);

/**
 * @brief Check if a capability is valid, has rights, and matches expected type.
 *
 * Additional Verification:
 * 4. Capability type matches expected_type (checks cap.pa field for non-memory caps)
 *
 * Note: For memory capabilities where pa is a physical address, use cap_check
 * or ensure expected_type handling accounts for aligned addresses.
 *
 * @param cap The capability to check
 * @param expected_type Expected capability type (e.g. EXO_CAP_IRQ)
 * @param required_rights Bitmask of rights required
 * @return 0 on success, -1 on failure
 */
int cap_check_type(exo_cap cap, uint32_t expected_type, uint32_t required_rights);

/**
 * @brief Check if a block capability is valid and has specific rights.
 *
 * Verifies:
 * 1. Capability possesses the required rights
 * 2. Capability is owned by the current process
 *
 * @param cap The block capability to check
 * @param required_rights Bitmask of rights required
 * @return 0 on success, -1 on failure
 */
int cap_check_block(exo_blockcap cap, uint32_t required_rights);

/**
 * @brief Check if a capability is owned by a specific process.
 *
 * @param cap The capability to check
 * @param pid The expected owner PID
 * @return 0 on success, -1 on failure
 */
int cap_check_owner(exo_cap cap, uint32_t pid);
