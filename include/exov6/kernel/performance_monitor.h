/**
 * @file performance_monitor.h
 * @brief Integrated Performance Monitoring System (Task 5.5.4 - Phase 5)
 *
 * Provides real-time monitoring and alerting for all adaptive systems:
 * - Capability cache performance
 * - SIMD optimization effectiveness
 * - Prefetch tuning efficiency
 * - Scheduler load balancing
 *
 * Features:
 * - Real-time performance dashboard
 * - Automatic regression detection
 * - Historical performance tracking
 * - Configurable alert thresholds
 * - Overhead: <0.2%
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <time.h>

#include "capability_cache_adaptive.h"
#include "capability_simd_adaptive.h"
#include "prefetch_tuning.h"
#include "scheduler_adaptive.h"

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 * CONFIGURATION
 ******************************************************************************/

/** Alert thresholds */
#define ALERT_CACHE_MISS_RATE_HIGH     0.30   /**< >30% cache miss rate */
#define ALERT_CACHE_MISS_RATE_LOW      0.95   /**< <5% cache miss rate (underutilized) */
#define ALERT_SIMD_SPEEDUP_LOW         1.2    /**< <20% SIMD speedup */
#define ALERT_PREFETCH_MISS_RATE_HIGH  0.15   /**< >15% prefetch miss rate */
#define ALERT_SCHED_IMBALANCE_HIGH     0.5    /**< >50% load imbalance */

/** Monitoring intervals */
#define MONITOR_INTERVAL_MS            1000   /**< 1 second */
#define MONITOR_HISTORY_SIZE           60     /**< Keep 60 samples (1 minute) */
#define MONITOR_REGRESSION_THRESHOLD   0.10   /**< 10% performance drop */

/*******************************************************************************
 * ALERT SYSTEM
 ******************************************************************************/

/**
 * @brief Alert severity level
 */
typedef enum {
    ALERT_NONE,      /**< No alert */
    ALERT_INFO,      /**< Informational */
    ALERT_WARNING,   /**< Warning - performance degraded */
    ALERT_CRITICAL   /**< Critical - severe performance issue */
} alert_severity_t;

/**
 * @brief Alert type
 */
typedef enum {
    ALERT_TYPE_CACHE_MISS_HIGH,      /**< Cache miss rate too high */
    ALERT_TYPE_CACHE_MISS_LOW,       /**< Cache miss rate too low (waste) */
    ALERT_TYPE_SIMD_INEFFECTIVE,     /**< SIMD not providing speedup */
    ALERT_TYPE_PREFETCH_INEFFECTIVE, /**< Prefetch not helping */
    ALERT_TYPE_SCHED_IMBALANCE,      /**< Load imbalance across CPUs */
    ALERT_TYPE_REGRESSION,           /**< Performance regression detected */
    ALERT_TYPE_MAX
} alert_type_t;

/**
 * @brief Performance alert
 */
typedef struct {
    alert_type_t type;         /**< Alert type */
    alert_severity_t severity; /**< Severity level */
    time_t timestamp;          /**< When alert was triggered */
    char message[256];         /**< Human-readable message */
    double metric_value;       /**< Current metric value */
    double threshold_value;    /**< Threshold that was exceeded */
} perf_alert_t;

/**
 * @brief Alert history
 */
typedef struct {
    perf_alert_t alerts[32];   /**< Ring buffer of recent alerts */
    uint32_t head;             /**< Next write position */
    uint32_t count;            /**< Total alerts (saturates at UINT32_MAX) */
    _Atomic uint32_t active;   /**< Number of active (unacknowledged) alerts */
} alert_history_t;

/*******************************************************************************
 * METRICS TRACKING
 ******************************************************************************/

/**
 * @brief Capability cache metrics snapshot
 */
typedef struct {
    double hit_rate;           /**< Cache hit rate (0.0-1.0) */
    uint32_t size_level;       /**< Current cache size level */
    uint64_t hits;             /**< Total hits */
    uint64_t misses;           /**< Total misses */
} cache_metrics_t;

/**
 * @brief SIMD metrics snapshot
 */
typedef struct {
    double avx512_speedup;     /**< AVX-512 speedup factor */
    double avx2_speedup;       /**< AVX2 speedup factor */
    uint32_t avx512_threshold; /**< Current AVX-512 threshold */
    uint32_t avx2_threshold;   /**< Current AVX2 threshold */
    bool calibrated;           /**< Calibration complete */
} simd_metrics_t;

/**
 * @brief Prefetch metrics snapshot
 */
typedef struct {
    uint32_t distance;         /**< Current prefetch distance */
    access_pattern_t pattern;  /**< Detected access pattern */
    double miss_rate;          /**< Cache miss rate */
    uint64_t prefetches;       /**< Prefetches issued */
} prefetch_metrics_t;

/**
 * @brief Scheduler metrics snapshot
 */
typedef struct {
    uint32_t steal_threshold;  /**< Current steal threshold */
    uint32_t batch_size;       /**< Current batch size */
    double avg_queue_length;   /**< Average queue length */
    double load_imbalance;     /**< Load imbalance (0.0-1.0) */
    uint64_t migrations;       /**< Total task migrations */
} sched_metrics_t;

/**
 * @brief Complete metrics snapshot
 */
typedef struct {
    time_t timestamp;          /**< Sample timestamp */
    cache_metrics_t cache;
    simd_metrics_t simd;
    prefetch_metrics_t prefetch;
    sched_metrics_t sched;
} metrics_snapshot_t;

/**
 * @brief Historical metrics tracking
 */
typedef struct {
    metrics_snapshot_t history[MONITOR_HISTORY_SIZE];
    uint32_t head;             /**< Next write position */
    uint32_t count;            /**< Number of valid samples */
} metrics_history_t;

/*******************************************************************************
 * PERFORMANCE MONITOR
 ******************************************************************************/

/**
 * @brief Performance monitor configuration
 */
typedef struct {
    /* Subsystem pointers */
    cap_cache_adaptive_t *cache;
    simd_adaptive_t *simd;
    prefetch_config_t *prefetch;
    sched_adaptive_t *sched;

    /* Monitoring state */
    _Atomic bool enabled;
    _Atomic bool alerts_enabled;

    /* Metrics and alerts */
    metrics_history_t history;
    alert_history_t alerts;

    /* Baseline for regression detection */
    metrics_snapshot_t baseline;
    bool baseline_set;
} perf_monitor_t;

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

/**
 * @brief Initialize performance monitor
 *
 * @param monitor  Performance monitor
 * @param cache    Capability cache (optional)
 * @param simd     SIMD optimizer (optional)
 * @param prefetch Prefetch tuner (optional)
 * @param sched    Scheduler (optional)
 * @return 0 on success, negative on error
 */
int perf_monitor_init(perf_monitor_t *monitor,
                      cap_cache_adaptive_t *cache,
                      simd_adaptive_t *simd,
                      prefetch_config_t *prefetch,
                      sched_adaptive_t *sched);

/**
 * @brief Destroy performance monitor
 *
 * @param monitor  Performance monitor
 */
void perf_monitor_destroy(perf_monitor_t *monitor);

/**
 * @brief Enable/disable monitoring
 *
 * @param monitor  Performance monitor
 * @param enable   true to enable, false to disable
 */
void perf_monitor_set_enabled(perf_monitor_t *monitor, bool enable);

/**
 * @brief Enable/disable alerts
 *
 * @param monitor  Performance monitor
 * @param enable   true to enable, false to disable
 */
void perf_monitor_set_alerts_enabled(perf_monitor_t *monitor, bool enable);

/*******************************************************************************
 * METRICS COLLECTION
 ******************************************************************************/

/**
 * @brief Collect current metrics snapshot
 *
 * Gathers metrics from all configured subsystems.
 *
 * @param monitor   Performance monitor
 * @param snapshot  Output snapshot
 */
void perf_monitor_collect(perf_monitor_t *monitor, metrics_snapshot_t *snapshot);

/**
 * @brief Record metrics snapshot in history
 *
 * @param monitor   Performance monitor
 * @param snapshot  Snapshot to record
 */
void perf_monitor_record(perf_monitor_t *monitor, const metrics_snapshot_t *snapshot);

/**
 * @brief Set performance baseline
 *
 * Sets the current metrics as the baseline for regression detection.
 *
 * @param monitor  Performance monitor
 */
void perf_monitor_set_baseline(perf_monitor_t *monitor);

/*******************************************************************************
 * ALERT MANAGEMENT
 ******************************************************************************/

/**
 * @brief Check for performance issues and generate alerts
 *
 * Analyzes current metrics against thresholds and historical data.
 *
 * @param monitor   Performance monitor
 * @param snapshot  Current metrics snapshot
 */
void perf_monitor_check_alerts(perf_monitor_t *monitor, const metrics_snapshot_t *snapshot);

/**
 * @brief Add alert to history
 *
 * @param monitor  Performance monitor
 * @param alert    Alert to add
 */
void perf_monitor_add_alert(perf_monitor_t *monitor, const perf_alert_t *alert);

/**
 * @brief Get active alerts
 *
 * @param monitor     Performance monitor
 * @param alerts      Output buffer
 * @param max_alerts  Maximum number of alerts to return
 * @return Number of active alerts
 */
uint32_t perf_monitor_get_active_alerts(const perf_monitor_t *monitor,
                                        perf_alert_t *alerts,
                                        uint32_t max_alerts);

/**
 * @brief Clear all active alerts
 *
 * @param monitor  Performance monitor
 */
void perf_monitor_clear_alerts(perf_monitor_t *monitor);

/*******************************************************************************
 * STATISTICS AND REPORTING
 ******************************************************************************/

/**
 * @brief Performance monitor statistics
 */
typedef struct {
    bool enabled;
    bool alerts_enabled;
    uint32_t history_samples;
    uint32_t total_alerts;
    uint32_t active_alerts;

    /* Current metrics */
    metrics_snapshot_t current;

    /* Baseline metrics (if set) */
    metrics_snapshot_t baseline;
    bool baseline_set;

    /* Recent alerts */
    perf_alert_t recent_alerts[8];
    uint32_t num_recent_alerts;
} perf_monitor_stats_t;

/**
 * @brief Get performance monitor statistics
 *
 * @param monitor  Performance monitor
 * @param stats    Output statistics
 */
void perf_monitor_get_stats(const perf_monitor_t *monitor, perf_monitor_stats_t *stats);

/**
 * @brief Print performance dashboard
 *
 * Displays current metrics, trends, and active alerts.
 *
 * @param monitor  Performance monitor
 */
void perf_monitor_print_dashboard(const perf_monitor_t *monitor);

/**
 * @brief Print alert history
 *
 * @param monitor  Performance monitor
 * @param count    Number of recent alerts to show
 */
void perf_monitor_print_alerts(const perf_monitor_t *monitor, uint32_t count);

/**
 * @brief Detect performance regressions
 *
 * Compares current performance against baseline.
 *
 * @param monitor  Performance monitor
 * @return true if regression detected
 */
bool perf_monitor_detect_regression(const perf_monitor_t *monitor);

#ifdef __cplusplus
}
#endif
