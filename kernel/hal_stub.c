/**
 * @file hal_stub.c
 * @brief Hardware Abstraction Layer stub implementations
 *
 * Temporary implementations until full HAL is linked.
 */

#include "types.h"

/* HAL structure - simplified stub */
struct hal_context {
    uint64_t cpu_id;
    void *current_process;
    uint64_t ticks;
};

/* Global HAL context - one per CPU in final implementation */
struct hal_context hal_context_storage = {
    .cpu_id = 0,
    .current_process = (void *)0,
    .ticks = 0,
};

/* HAL current context pointer */
struct hal_context *hal_current = &hal_context_storage;

/* HAL global pointer (used by exo_impl_c17.c) */
struct hal_context *hal = &hal_context_storage;

/**
 * Get current HAL context
 * TODO: Replace with architecture-specific implementation
 */
struct hal_context *hal_get_current(void)
{
    return &hal_context_storage;
}
