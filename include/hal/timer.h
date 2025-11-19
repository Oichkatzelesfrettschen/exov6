#pragma once

/**
 * @file hal/timer.h
 * @brief Hardware Abstraction Layer for timer and clock operations
 * 
 * Pure C17 implementation for platform-agnostic timing.
 */

#include <stdint.h>
#include <stdbool.h>

/**
 * @brief Timer frequency information
 */
typedef struct {
    uint64_t frequency_hz;     // Timer frequency in Hz
    uint64_t resolution_ns;    // Timer resolution in nanoseconds
    bool is_monotonic;         // True if timer is monotonic
    bool is_per_cpu;          // True if timer is per-CPU
} hal_timer_info_t;

/**
 * @brief Timer callback function type
 */
typedef void (*hal_timer_callback_t)(void* data);

/**
 * @brief Initialize timer subsystem
 * @return 0 on success, negative on error
 */
int32_t hal_timer_init(void);

/**
 * @brief Get timer information
 * @param info Pointer to fill with timer info
 * @return 0 on success, negative on error
 */
int32_t hal_timer_get_info(hal_timer_info_t* info);

/**
 * @brief Get current timer value
 * @return Current timer counter value
 */
uint64_t hal_timer_read(void);

/**
 * @brief Get current time in nanoseconds
 * @return Time since boot in nanoseconds
 */
uint64_t hal_timer_get_ns(void);

/**
 * @brief Get current time in microseconds
 * @return Time since boot in microseconds
 */
static inline uint64_t hal_timer_get_us(void) {
    return hal_timer_get_ns() / 1000;
}

/**
 * @brief Get current time in milliseconds
 * @return Time since boot in milliseconds
 */
static inline uint64_t hal_timer_get_ms(void) {
    return hal_timer_get_ns() / 1000000;
}

/**
 * @brief Busy-wait delay in nanoseconds
 * @param ns Nanoseconds to delay
 */
void hal_timer_delay_ns(uint64_t ns);

/**
 * @brief Busy-wait delay in microseconds
 * @param us Microseconds to delay
 */
static inline void hal_timer_delay_us(uint64_t us) {
    hal_timer_delay_ns(us * 1000);
}

/**
 * @brief Busy-wait delay in milliseconds
 * @param ms Milliseconds to delay
 */
static inline void hal_timer_delay_ms(uint64_t ms) {
    hal_timer_delay_ns(ms * 1000000);
}

/**
 * @brief Set one-shot timer
 * @param ns Nanoseconds until callback
 * @param callback Function to call
 * @param data Data to pass to callback
 * @return Timer ID or negative on error
 */
int32_t hal_timer_oneshot(uint64_t ns, hal_timer_callback_t callback, void* data);

/**
 * @brief Set periodic timer
 * @param ns Period in nanoseconds
 * @param callback Function to call
 * @param data Data to pass to callback
 * @return Timer ID or negative on error
 */
int32_t hal_timer_periodic(uint64_t ns, hal_timer_callback_t callback, void* data);

/**
 * @brief Cancel timer
 * @param timer_id Timer ID from oneshot/periodic
 * @return 0 on success, negative on error
 */
int32_t hal_timer_cancel(int32_t timer_id);

/**
 * @brief Get CPU timestamp counter
 * @return CPU-specific timestamp value
 */
uint64_t hal_timer_read_tsc(void);

/**
 * @brief Convert TSC to nanoseconds
 * @param tsc TSC value from hal_timer_read_tsc
 * @return Nanoseconds
 */
uint64_t hal_timer_tsc_to_ns(uint64_t tsc);

// High-resolution timing structure
typedef struct {
    uint64_t start;
    uint64_t end;
    uint64_t elapsed_ns;
} hal_timing_t;

/**
 * @brief Start timing measurement
 * @param timing Timing structure to initialize
 */
static inline void hal_timing_start(hal_timing_t* timing) {
    timing->start = hal_timer_read_tsc();
}

/**
 * @brief End timing measurement
 * @param timing Timing structure
 * @return Elapsed nanoseconds
 */
static inline uint64_t hal_timing_end(hal_timing_t* timing) {
    timing->end = hal_timer_read_tsc();
    timing->elapsed_ns = hal_timer_tsc_to_ns(timing->end - timing->start);
    return timing->elapsed_ns;
}

// Compile-time assertions
_Static_assert(sizeof(hal_timing_t) <= 64, "Timing structure too large");
