/**
 * @file scheduler_adaptive.h
 * @brief Adaptive Scheduler Optimization (Task 5.5.4 - Phase 4)
 *
 * Dynamically adapts scheduling parameters based on runtime load:
 * - Load-based work stealing thresholds
 * - Dynamic batch size adjustment
 * - Adaptive queue length triggers
 *
 * Expected Performance:
 * - 5-10% improvement for mixed workloads
 * - Better load balancing across CPUs
 * - Reduced contention overhead
 * - Overhead: <0.5%
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/** Work stealing thresholds */
#define STEAL_THRESHOLD_LOW     2    /**< Low load - conservative stealing */
#define STEAL_THRESHOLD_MEDIUM  4    /**< Medium load - moderate stealing */
#define STEAL_THRESHOLD_HIGH    8    /**< High load - aggressive stealing */

/** Batch size configuration */
#define BATCH_SIZE_MIN          1    /**< Minimum batch size */
#define BATCH_SIZE_SMALL        4    /**< Small batches */
#define BATCH_SIZE_MEDIUM       8    /**< Medium batches */
#define BATCH_SIZE_LARGE        16   /**< Large batches */
#define BATCH_SIZE_MAX          32   /**< Maximum batch size */

/** Queue length thresholds */
#define QUEUE_EMPTY             0    /**< Queue is empty */
#define QUEUE_LOW               8    /**< Low queue depth */
#define QUEUE_MEDIUM            32   /**< Medium queue depth */
#define QUEUE_HIGH              128  /**< High queue depth */

/** Tuning parameters */
#define SCHED_TUNE_INTERVAL     10000  /**< Samples before tuning */
#define SCHED_LOAD_WINDOW       1000   /**< Load averaging window */

/*******************************************************************************
 * LOAD TRACKING
 ******************************************************************************/

/**
 * @brief CPU load level
 */
typedef enum {
    LOAD_IDLE,        /**< CPU mostly idle */
    LOAD_LOW,         /**< Light load */
    LOAD_MEDIUM,      /**< Moderate load */
    LOAD_HIGH,        /**< Heavy load */
    LOAD_SATURATED    /**< CPU saturated */
} cpu_load_level_t;

/**
 * @brief Per-CPU load tracker
 */
typedef struct {
    /** Queue statistics */
    _Atomic uint32_t queue_length;       /**< Current queue depth */
    _Atomic uint64_t enqueues;           /**< Total enqueues */
    _Atomic uint64_t dequeues;           /**< Total dequeues */
    _Atomic uint64_t steals_attempted;   /**< Work steal attempts */
    _Atomic uint64_t steals_succeeded;   /**< Successful steals */

    /** Load metrics */
    uint32_t queue_samples[16];          /**< Ring buffer of queue lengths */
    uint32_t sample_index;               /**< Current sample index */
    double avg_queue_length;             /**< Rolling average */
    cpu_load_level_t load_level;         /**< Detected load level */

    /** Idle tracking */
    _Atomic uint64_t idle_cycles;        /**< Cycles spent idle */
    _Atomic uint64_t busy_cycles;        /**< Cycles spent busy */
} cpu_load_tracker_t;

/*******************************************************************************
 * SCHEDULER CONFIGURATION
 ******************************************************************************/

/**
 * @brief Adaptive scheduler configuration
 */
typedef struct {
    /** Current settings */
    _Atomic uint32_t steal_threshold;    /**< Current work stealing threshold */
    _Atomic uint32_t batch_size;         /**< Current batch size */
    _Atomic uint32_t queue_high_mark;    /**< High water mark for queue */

    /** Per-CPU load tracking */
    cpu_load_tracker_t trackers[256];    /**< Per-CPU trackers (max 256 CPUs) */
    uint32_t num_cpus;                   /**< Number of CPUs */

    /** Global statistics */
    _Atomic uint64_t total_migrations;   /**< Task migrations */
    _Atomic uint64_t total_stalls;       /**< Scheduler stalls */

    /** Tuning state */
    uint64_t samples_since_tune;         /**< Samples since last tune */
    uint32_t consecutive_adjustments;    /**< Oscillation prevention */

    /** Control */
    _Atomic bool enabled;                /**< Adaptation enabled */
} sched_adaptive_t;

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

/**
 * @brief Initialize adaptive scheduler
 *
 * @param sched    Scheduler configuration
 * @param num_cpus Number of CPUs in system
 * @return 0 on success, negative on error
 */
int sched_adaptive_init(sched_adaptive_t *sched, uint32_t num_cpus);

/**
 * @brief Destroy adaptive scheduler
 *
 * @param sched  Scheduler configuration
 */
void sched_adaptive_destroy(sched_adaptive_t *sched);

/**
 * @brief Enable/disable scheduler adaptation
 *
 * @param sched   Scheduler configuration
 * @param enable  true to enable, false to disable
 */
void sched_adaptive_set_enabled(sched_adaptive_t *sched, bool enable);

/*******************************************************************************
 * LOAD TRACKING
 ******************************************************************************/

/**
 * @brief Update queue length sample
 *
 * @param tracker  CPU load tracker
 * @param length   Current queue length
 */
static inline void sched_update_queue_sample(cpu_load_tracker_t *tracker, uint32_t length)
{
    if (!tracker) return;

    /* Store in ring buffer */
    tracker->queue_samples[tracker->sample_index] = length;
    tracker->sample_index = (tracker->sample_index + 1) % 16;

    /* Compute rolling average */
    uint64_t sum = 0;
    for (int i = 0; i < 16; i++) {
        sum += tracker->queue_samples[i];
    }
    tracker->avg_queue_length = (double)sum / 16.0;

    /* Classify load level */
    if (tracker->avg_queue_length < 1.0) {
        tracker->load_level = LOAD_IDLE;
    } else if (tracker->avg_queue_length < 8.0) {
        tracker->load_level = LOAD_LOW;
    } else if (tracker->avg_queue_length < 32.0) {
        tracker->load_level = LOAD_MEDIUM;
    } else if (tracker->avg_queue_length < 128.0) {
        tracker->load_level = LOAD_HIGH;
    } else {
        tracker->load_level = LOAD_SATURATED;
    }
}

/**
 * @brief Record task enqueue
 *
 * @param sched  Scheduler configuration
 * @param cpu    CPU number
 */
static inline void sched_record_enqueue(sched_adaptive_t *sched, uint32_t cpu)
{
    if (!sched || cpu >= sched->num_cpus) return;

    cpu_load_tracker_t *tracker = &sched->trackers[cpu];

    uint32_t new_len = atomic_fetch_add(&tracker->queue_length, 1) + 1;
    atomic_fetch_add(&tracker->enqueues, 1);

    /* Periodically sample queue length */
    if (atomic_load(&tracker->enqueues) % 64 == 0) {
        sched_update_queue_sample(tracker, new_len);
    }
}

/**
 * @brief Record task dequeue
 *
 * @param sched  Scheduler configuration
 * @param cpu    CPU number
 */
static inline void sched_record_dequeue(sched_adaptive_t *sched, uint32_t cpu)
{
    if (!sched || cpu >= sched->num_cpus) return;

    cpu_load_tracker_t *tracker = &sched->trackers[cpu];

    uint32_t old_len = atomic_load(&tracker->queue_length);
    if (old_len > 0) {
        atomic_fetch_sub(&tracker->queue_length, 1);
    }
    atomic_fetch_add(&tracker->dequeues, 1);
}

/**
 * @brief Get CPU load level
 *
 * @param sched  Scheduler configuration
 * @param cpu    CPU number
 * @return Load level
 */
static inline cpu_load_level_t sched_get_load_level(const sched_adaptive_t *sched, uint32_t cpu)
{
    if (!sched || cpu >= sched->num_cpus) return LOAD_IDLE;
    return sched->trackers[cpu].load_level;
}

/**
 * @brief Get average queue length
 *
 * @param sched  Scheduler configuration
 * @param cpu    CPU number
 * @return Average queue length
 */
static inline double sched_get_avg_queue_length(const sched_adaptive_t *sched, uint32_t cpu)
{
    if (!sched || cpu >= sched->num_cpus) return 0.0;
    return sched->trackers[cpu].avg_queue_length;
}

/*******************************************************************************
 * WORK STEALING
 ******************************************************************************/

/**
 * @brief Check if work stealing should be attempted
 *
 * @param sched      Scheduler configuration
 * @param local_cpu  Local CPU number
 * @param remote_cpu Remote CPU number
 * @return true if stealing should be attempted
 */
static inline bool sched_should_steal(const sched_adaptive_t *sched,
                                      uint32_t local_cpu, uint32_t remote_cpu)
{
    if (!sched || !atomic_load(&sched->enabled)) return false;
    if (local_cpu >= sched->num_cpus || remote_cpu >= sched->num_cpus) return false;

    /* Get local and remote queue lengths */
    uint32_t local_len = atomic_load(&sched->trackers[local_cpu].queue_length);
    uint32_t remote_len = atomic_load(&sched->trackers[remote_cpu].queue_length);

    /* Only steal if remote has more than threshold */
    uint32_t threshold = atomic_load(&sched->steal_threshold);

    /* Steal if remote is loaded and we're idle */
    if (local_len == 0 && remote_len >= threshold) {
        return true;
    }

    /* Steal if remote has significantly more work */
    if (remote_len >= threshold && remote_len > local_len * 2) {
        return true;
    }

    return false;
}

/**
 * @brief Record work steal attempt
 *
 * @param sched      Scheduler configuration
 * @param cpu        CPU number
 * @param succeeded  Whether steal succeeded
 */
static inline void sched_record_steal(sched_adaptive_t *sched, uint32_t cpu, bool succeeded)
{
    if (!sched || cpu >= sched->num_cpus) return;

    cpu_load_tracker_t *tracker = &sched->trackers[cpu];
    atomic_fetch_add(&tracker->steals_attempted, 1);

    if (succeeded) {
        atomic_fetch_add(&tracker->steals_succeeded, 1);
        atomic_fetch_add(&sched->total_migrations, 1);
    }
}

/*******************************************************************************
 * BATCH SIZE ADAPTATION
 ******************************************************************************/

/**
 * @brief Get recommended batch size
 *
 * @param sched  Scheduler configuration
 * @param cpu    CPU number
 * @return Recommended batch size
 */
static inline uint32_t sched_get_batch_size(const sched_adaptive_t *sched, uint32_t cpu)
{
    if (!sched || !atomic_load(&sched->enabled)) {
        return BATCH_SIZE_MEDIUM;
    }

    if (cpu >= sched->num_cpus) return BATCH_SIZE_MEDIUM;

    cpu_load_level_t load = sched->trackers[cpu].load_level;

    /* Adapt batch size to load level */
    switch (load) {
        case LOAD_IDLE:
        case LOAD_LOW:
            /* Small batches for low latency */
            return BATCH_SIZE_SMALL;

        case LOAD_MEDIUM:
            /* Medium batches for balance */
            return BATCH_SIZE_MEDIUM;

        case LOAD_HIGH:
        case LOAD_SATURATED:
            /* Large batches for throughput */
            return BATCH_SIZE_LARGE;

        default:
            return BATCH_SIZE_MEDIUM;
    }
}

/*******************************************************************************
 * TUNING
 ******************************************************************************/

/**
 * @brief Tune scheduler parameters
 *
 * Adjusts steal threshold, batch size, and queue marks based on
 * observed load patterns and performance.
 *
 * @param sched  Scheduler configuration
 */
void sched_adaptive_tune(sched_adaptive_t *sched);

/**
 * @brief Compute recommended steal threshold
 *
 * @param sched  Scheduler configuration
 * @return Recommended threshold
 */
uint32_t sched_compute_steal_threshold(const sched_adaptive_t *sched);

/*******************************************************************************
 * STATISTICS
 ******************************************************************************/

/**
 * @brief Scheduler statistics
 */
typedef struct {
    bool enabled;
    uint32_t num_cpus;
    uint32_t steal_threshold;
    uint32_t batch_size;
    uint64_t total_migrations;
    uint64_t total_stalls;

    /** Per-CPU stats */
    struct {
        uint32_t queue_length;
        double avg_queue_length;
        cpu_load_level_t load_level;
        uint64_t steals_attempted;
        uint64_t steals_succeeded;
        double steal_success_rate;
    } cpu_stats[256];
} sched_stats_t;

/**
 * @brief Get scheduler statistics
 *
 * @param sched  Scheduler configuration
 * @param stats  Output statistics
 */
void sched_get_stats(const sched_adaptive_t *sched, sched_stats_t *stats);

/**
 * @brief Print scheduler statistics
 *
 * @param sched  Scheduler configuration
 */
void sched_print_stats(const sched_adaptive_t *sched);

#ifdef __cplusplus
}
#endif
