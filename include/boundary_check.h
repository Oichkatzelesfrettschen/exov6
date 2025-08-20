/**
 * @file boundary_check.h
 * @brief Security boundary enforcement for exokernel layers
 *
 * Provides runtime checks and validation for security boundaries
 * between kernel, libOS, and userland components.
 */

#pragma once

#include "types.h"
#include "exo.h"
#include <stdint.h>

/**
 * @brief Validate that a capability has required rights for an operation.
 *
 * @param cap The capability to check
 * @param required_rights Bitmask of required rights
 * @param operation_name Description for logging/debugging
 * @return 1 if authorized, 0 if denied
 */
[[nodiscard]] int boundary_check_capability_rights(exo_cap cap, 
                                                   uint32_t required_rights,
                                                   const char *operation_name);

/**
 * @brief Validate that a user buffer is within process bounds.
 *
 * @param user_ptr Pointer from user space
 * @param len Length of buffer
 * @param access_type R/W/X access type
 * @return 1 if valid, 0 if invalid
 */
[[nodiscard]] int boundary_check_user_buffer(const void *user_ptr, 
                                             size_t len, 
                                             uint32_t access_type);

/**
 * @brief Verify IPC channel authentication before message processing.
 *
 * @param chan Lattice IPC channel
 * @param peer_id Expected peer identifier  
 * @return 1 if authenticated, 0 if not
 */
[[nodiscard]] int boundary_check_ipc_auth(const void *chan, 
                                          uint32_t peer_id);

/**
 * @brief Log security boundary violations for audit.
 *
 * @param violation_type Type of boundary violation
 * @param context Additional context information
 */
void boundary_log_violation(const char *violation_type, 
                           const char *context);