/**
 * @file performance_monitor.c
 * @brief Performance Monitoring Implementation (Task 5.5.4 - Phase 5)
 */

#include "performance_monitor.h"
#include <stdio.h>
#include <string.h>
#include <math.h>

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

int perf_monitor_init(perf_monitor_t *monitor,
                      cap_cache_adaptive_t *cache,
                      simd_adaptive_t *simd,
                      prefetch_config_t *prefetch,
                      sched_adaptive_t *sched)
{
    if (!monitor) return -1;

    memset(monitor, 0, sizeof(*monitor));

    monitor->cache = cache;
    monitor->simd = simd;
    monitor->prefetch = prefetch;
    monitor->sched = sched;

    atomic_store(&monitor->enabled, true);
    atomic_store(&monitor->alerts_enabled, true);

    return 0;
}

void perf_monitor_destroy(perf_monitor_t *monitor)
{
    if (!monitor) return;
    atomic_store(&monitor->enabled, false);
}

void perf_monitor_set_enabled(perf_monitor_t *monitor, bool enable)
{
    if (!monitor) return;
    atomic_store(&monitor->enabled, enable);
}

void perf_monitor_set_alerts_enabled(perf_monitor_t *monitor, bool enable)
{
    if (!monitor) return;
    atomic_store(&monitor->alerts_enabled, enable);
}

/*******************************************************************************
 * METRICS COLLECTION
 ******************************************************************************/

void perf_monitor_collect(perf_monitor_t *monitor, metrics_snapshot_t *snapshot)
{
    if (!monitor || !snapshot) return;

    memset(snapshot, 0, sizeof(*snapshot));
    snapshot->timestamp = time(NULL);

    /* Collect cache metrics */
    if (monitor->cache) {
        cap_cache_adaptive_stats_t cache_stats;
        cap_cache_get_adaptive_stats(monitor->cache, 0, &cache_stats);

        uint64_t hits = atomic_load(&cache_stats.hits_since_tune);
        uint64_t misses = atomic_load(&cache_stats.misses_since_tune);
        uint64_t total = hits + misses;

        snapshot->cache.hit_rate = (total > 0) ? (double)hits / total : 0.0;
        snapshot->cache.size_level = atomic_load(&cache_stats.current_level);
        snapshot->cache.hits = hits;
        snapshot->cache.misses = misses;
    }

    /* Collect SIMD metrics */
    if (monitor->simd) {
        simd_stats_t simd_stats;
        simd_get_stats(monitor->simd, &simd_stats);

        snapshot->simd.avx512_speedup = simd_stats.avx512_speedup;
        snapshot->simd.avx2_speedup = simd_stats.avx2_speedup;
        snapshot->simd.avx512_threshold = simd_stats.avx512_threshold;
        snapshot->simd.avx2_threshold = simd_stats.avx2_threshold;
        snapshot->simd.calibrated = simd_stats.calibrated;
    }

    /* Collect prefetch metrics */
    if (monitor->prefetch) {
        prefetch_stats_t prefetch_stats;
        prefetch_get_stats(monitor->prefetch, &prefetch_stats);

        snapshot->prefetch.distance = prefetch_stats.current_distance;
        snapshot->prefetch.pattern = prefetch_stats.detected_pattern;
        snapshot->prefetch.miss_rate = prefetch_stats.miss_rate;
        snapshot->prefetch.prefetches = prefetch_stats.prefetches_issued;
    }

    /* Collect scheduler metrics */
    if (monitor->sched) {
        sched_stats_t sched_stats;
        sched_get_stats(monitor->sched, &sched_stats);

        snapshot->sched.steal_threshold = sched_stats.steal_threshold;
        snapshot->sched.batch_size = sched_stats.batch_size;
        snapshot->sched.migrations = sched_stats.total_migrations;

        /* Compute average queue length and load imbalance */
        double total_avg = 0.0;
        double max_load = 0.0;
        double min_load = 1e9;

        for (uint32_t i = 0; i < sched_stats.num_cpus; i++) {
            double load = sched_stats.cpu_stats[i].avg_queue_length;
            total_avg += load;
            if (load > max_load) max_load = load;
            if (load < min_load) min_load = load;
        }

        total_avg /= sched_stats.num_cpus;
        snapshot->sched.avg_queue_length = total_avg;

        /* Imbalance = (max - min) / max */
        snapshot->sched.load_imbalance = (max_load > 0) ? (max_load - min_load) / max_load : 0.0;
    }
}

void perf_monitor_record(perf_monitor_t *monitor, const metrics_snapshot_t *snapshot)
{
    if (!monitor || !snapshot) return;

    metrics_history_t *hist = &monitor->history;

    /* Store in ring buffer */
    hist->history[hist->head] = *snapshot;
    hist->head = (hist->head + 1) % MONITOR_HISTORY_SIZE;

    if (hist->count < MONITOR_HISTORY_SIZE) {
        hist->count++;
    }
}

void perf_monitor_set_baseline(perf_monitor_t *monitor)
{
    if (!monitor) return;

    perf_monitor_collect(monitor, &monitor->baseline);
    monitor->baseline_set = true;
}

/*******************************************************************************
 * ALERT MANAGEMENT
 ******************************************************************************/

void perf_monitor_add_alert(perf_monitor_t *monitor, const perf_alert_t *alert)
{
    if (!monitor || !alert) return;

    alert_history_t *hist = &monitor->alerts;

    /* Store in ring buffer */
    hist->alerts[hist->head] = *alert;
    hist->head = (hist->head + 1) % 32;

    if (hist->count < UINT32_MAX) {
        hist->count++;
    }

    atomic_fetch_add(&hist->active, 1);
}

void perf_monitor_check_alerts(perf_monitor_t *monitor, const metrics_snapshot_t *snapshot)
{
    if (!monitor || !snapshot) return;
    if (!atomic_load(&monitor->alerts_enabled)) return;

    perf_alert_t alert;
    memset(&alert, 0, sizeof(alert));
    alert.timestamp = snapshot->timestamp;

    /* Check cache miss rate */
    if (snapshot->cache.hit_rate < (1.0 - ALERT_CACHE_MISS_RATE_HIGH)) {
        alert.type = ALERT_TYPE_CACHE_MISS_HIGH;
        alert.severity = ALERT_WARNING;
        alert.metric_value = 1.0 - snapshot->cache.hit_rate;
        alert.threshold_value = ALERT_CACHE_MISS_RATE_HIGH;
        snprintf(alert.message, sizeof(alert.message),
                 "Cache miss rate high: %.1f%% (threshold: %.1f%%)",
                 alert.metric_value * 100.0, alert.threshold_value * 100.0);
        perf_monitor_add_alert(monitor, &alert);
    }

    /* Check if cache is underutilized */
    if (snapshot->cache.hit_rate > ALERT_CACHE_MISS_RATE_LOW) {
        alert.type = ALERT_TYPE_CACHE_MISS_LOW;
        alert.severity = ALERT_INFO;
        alert.metric_value = 1.0 - snapshot->cache.hit_rate;
        alert.threshold_value = 1.0 - ALERT_CACHE_MISS_RATE_LOW;
        snprintf(alert.message, sizeof(alert.message),
                 "Cache miss rate very low: %.1f%% (may be oversized)",
                 alert.metric_value * 100.0);
        perf_monitor_add_alert(monitor, &alert);
    }

    /* Check SIMD effectiveness */
    if (snapshot->simd.calibrated && snapshot->simd.avx2_speedup < ALERT_SIMD_SPEEDUP_LOW) {
        alert.type = ALERT_TYPE_SIMD_INEFFECTIVE;
        alert.severity = ALERT_WARNING;
        alert.metric_value = snapshot->simd.avx2_speedup;
        alert.threshold_value = ALERT_SIMD_SPEEDUP_LOW;
        snprintf(alert.message, sizeof(alert.message),
                 "SIMD speedup low: %.2fx (threshold: %.2fx)",
                 alert.metric_value, alert.threshold_value);
        perf_monitor_add_alert(monitor, &alert);
    }

    /* Check prefetch effectiveness */
    if (snapshot->prefetch.miss_rate > ALERT_PREFETCH_MISS_RATE_HIGH) {
        alert.type = ALERT_TYPE_PREFETCH_INEFFECTIVE;
        alert.severity = ALERT_WARNING;
        alert.metric_value = snapshot->prefetch.miss_rate;
        alert.threshold_value = ALERT_PREFETCH_MISS_RATE_HIGH;
        snprintf(alert.message, sizeof(alert.message),
                 "Prefetch miss rate high: %.1f%% (threshold: %.1f%%)",
                 alert.metric_value * 100.0, alert.threshold_value * 100.0);
        perf_monitor_add_alert(monitor, &alert);
    }

    /* Check scheduler load imbalance */
    if (snapshot->sched.load_imbalance > ALERT_SCHED_IMBALANCE_HIGH) {
        alert.type = ALERT_TYPE_SCHED_IMBALANCE;
        alert.severity = ALERT_WARNING;
        alert.metric_value = snapshot->sched.load_imbalance;
        alert.threshold_value = ALERT_SCHED_IMBALANCE_HIGH;
        snprintf(alert.message, sizeof(alert.message),
                 "Scheduler load imbalance: %.1f%% (threshold: %.1f%%)",
                 alert.metric_value * 100.0, alert.threshold_value * 100.0);
        perf_monitor_add_alert(monitor, &alert);
    }
}

uint32_t perf_monitor_get_active_alerts(const perf_monitor_t *monitor,
                                        perf_alert_t *alerts,
                                        uint32_t max_alerts)
{
    if (!monitor || !alerts || max_alerts == 0) return 0;

    uint32_t active = atomic_load(&monitor->alerts.active);
    if (active == 0) return 0;

    /* Return up to max_alerts most recent alerts */
    uint32_t count = (active < max_alerts) ? active : max_alerts;
    uint32_t start = (monitor->alerts.head + 32 - count) % 32;

    for (uint32_t i = 0; i < count; i++) {
        alerts[i] = monitor->alerts.alerts[(start + i) % 32];
    }

    return count;
}

void perf_monitor_clear_alerts(perf_monitor_t *monitor)
{
    if (!monitor) return;
    atomic_store(&monitor->alerts.active, 0);
}

/*******************************************************************************
 * REGRESSION DETECTION
 ******************************************************************************/

bool perf_monitor_detect_regression(const perf_monitor_t *monitor)
{
    if (!monitor || !monitor->baseline_set) return false;

    /* Collect current metrics */
    metrics_snapshot_t current;
    perf_monitor_collect((perf_monitor_t *)monitor, &current);

    /* Compare against baseline */
    bool regression = false;

    /* Cache performance regression */
    if (current.cache.hit_rate < monitor->baseline.cache.hit_rate * (1.0 - MONITOR_REGRESSION_THRESHOLD)) {
        regression = true;
    }

    /* SIMD performance regression */
    if (current.simd.avx2_speedup < monitor->baseline.simd.avx2_speedup * (1.0 - MONITOR_REGRESSION_THRESHOLD)) {
        regression = true;
    }

    /* Prefetch performance regression (higher miss rate is worse) */
    if (current.prefetch.miss_rate > monitor->baseline.prefetch.miss_rate * (1.0 + MONITOR_REGRESSION_THRESHOLD)) {
        regression = true;
    }

    /* Scheduler performance regression (higher imbalance is worse) */
    if (current.sched.load_imbalance > monitor->baseline.sched.load_imbalance * (1.0 + MONITOR_REGRESSION_THRESHOLD)) {
        regression = true;
    }

    return regression;
}

/*******************************************************************************
 * STATISTICS AND REPORTING
 ******************************************************************************/

void perf_monitor_get_stats(const perf_monitor_t *monitor, perf_monitor_stats_t *stats)
{
    if (!monitor || !stats) return;

    memset(stats, 0, sizeof(*stats));

    stats->enabled = atomic_load(&monitor->enabled);
    stats->alerts_enabled = atomic_load(&monitor->alerts_enabled);
    stats->history_samples = monitor->history.count;
    stats->total_alerts = monitor->alerts.count;
    stats->active_alerts = atomic_load(&monitor->alerts.active);

    /* Collect current metrics */
    perf_monitor_collect((perf_monitor_t *)monitor, &stats->current);

    /* Copy baseline if set */
    if (monitor->baseline_set) {
        stats->baseline = monitor->baseline;
        stats->baseline_set = true;
    }

    /* Get recent alerts */
    stats->num_recent_alerts = perf_monitor_get_active_alerts(monitor,
                                                               stats->recent_alerts,
                                                               8);
}

void perf_monitor_print_dashboard(const perf_monitor_t *monitor)
{
    if (!monitor) return;

    printf("================================================================================\n");
    printf("PERFORMANCE MONITORING DASHBOARD\n");
    printf("================================================================================\n\n");

    perf_monitor_stats_t stats;
    perf_monitor_get_stats(monitor, &stats);

    printf("Monitor Status:\n");
    printf("  Enabled:           %s\n", stats.enabled ? "Yes" : "No");
    printf("  Alerts:            %s\n", stats.alerts_enabled ? "Yes" : "No");
    printf("  History Samples:   %u\n", stats.history_samples);
    printf("  Active Alerts:     %u\n", stats.active_alerts);
    printf("\n");

    /* Cache metrics */
    printf("Capability Cache:\n");
    printf("  Hit Rate:          %.1f%%\n", stats.current.cache.hit_rate * 100.0);
    printf("  Size Level:        %u\n", stats.current.cache.size_level);
    printf("  Hits:              %lu\n", stats.current.cache.hits);
    printf("  Misses:            %lu\n", stats.current.cache.misses);
    printf("\n");

    /* SIMD metrics */
    printf("SIMD Optimization:\n");
    printf("  Calibrated:        %s\n", stats.current.simd.calibrated ? "Yes" : "No");
    printf("  AVX-512 Speedup:   %.2fx\n", stats.current.simd.avx512_speedup);
    printf("  AVX2 Speedup:      %.2fx\n", stats.current.simd.avx2_speedup);
    printf("  AVX-512 Threshold: %u\n", stats.current.simd.avx512_threshold);
    printf("  AVX2 Threshold:    %u\n", stats.current.simd.avx2_threshold);
    printf("\n");

    /* Prefetch metrics */
    printf("Prefetch Tuning:\n");
    printf("  Distance:          %u cache lines\n", stats.current.prefetch.distance);

    const char *pattern_str;
    switch (stats.current.prefetch.pattern) {
        case PATTERN_SEQUENTIAL: pattern_str = "Sequential"; break;
        case PATTERN_STRIDED:    pattern_str = "Strided"; break;
        case PATTERN_RANDOM:     pattern_str = "Random"; break;
        default:                 pattern_str = "Unknown"; break;
    }
    printf("  Pattern:           %s\n", pattern_str);
    printf("  Miss Rate:         %.1f%%\n", stats.current.prefetch.miss_rate * 100.0);
    printf("  Prefetches Issued: %lu\n", stats.current.prefetch.prefetches);
    printf("\n");

    /* Scheduler metrics */
    printf("Adaptive Scheduler:\n");
    printf("  Steal Threshold:   %u tasks\n", stats.current.sched.steal_threshold);
    printf("  Batch Size:        %u tasks\n", stats.current.sched.batch_size);
    printf("  Avg Queue Length:  %.1f tasks\n", stats.current.sched.avg_queue_length);
    printf("  Load Imbalance:    %.1f%%\n", stats.current.sched.load_imbalance * 100.0);
    printf("  Migrations:        %lu\n", stats.current.sched.migrations);
    printf("\n");

    /* Baseline comparison */
    if (stats.baseline_set) {
        printf("Baseline Comparison:\n");

        double cache_delta = (stats.current.cache.hit_rate - stats.baseline.cache.hit_rate) * 100.0;
        printf("  Cache Hit Rate:    %+.1f%%\n", cache_delta);

        double simd_delta = stats.current.simd.avx2_speedup - stats.baseline.simd.avx2_speedup;
        printf("  SIMD Speedup:      %+.2fx\n", simd_delta);

        double prefetch_delta = (stats.current.prefetch.miss_rate - stats.baseline.prefetch.miss_rate) * 100.0;
        printf("  Prefetch Miss:     %+.1f%%\n", prefetch_delta);

        double sched_delta = (stats.current.sched.load_imbalance - stats.baseline.sched.load_imbalance) * 100.0;
        printf("  Load Imbalance:    %+.1f%%\n", sched_delta);

        bool regression = perf_monitor_detect_regression(monitor);
        printf("  Regression:        %s\n", regression ? "DETECTED" : "None");
        printf("\n");
    }

    /* Active alerts */
    if (stats.active_alerts > 0) {
        printf("ACTIVE ALERTS:\n");
        for (uint32_t i = 0; i < stats.num_recent_alerts && i < 5; i++) {
            const perf_alert_t *alert = &stats.recent_alerts[i];

            const char *severity_str;
            switch (alert->severity) {
                case ALERT_INFO:     severity_str = "INFO"; break;
                case ALERT_WARNING:  severity_str = "WARN"; break;
                case ALERT_CRITICAL: severity_str = "CRIT"; break;
                default:             severity_str = "????"; break;
            }

            printf("  [%s] %s\n", severity_str, alert->message);
        }
        printf("\n");
    }

    printf("================================================================================\n");
}

void perf_monitor_print_alerts(const perf_monitor_t *monitor, uint32_t count)
{
    if (!monitor) return;

    printf("================================================================================\n");
    printf("PERFORMANCE ALERT HISTORY\n");
    printf("================================================================================\n\n");

    perf_alert_t alerts[32];
    uint32_t num = perf_monitor_get_active_alerts(monitor, alerts, (count < 32) ? count : 32);

    if (num == 0) {
        printf("No active alerts.\n");
    } else {
        for (uint32_t i = 0; i < num; i++) {
            const perf_alert_t *alert = &alerts[i];

            const char *severity_str;
            switch (alert->severity) {
                case ALERT_INFO:     severity_str = "INFO    "; break;
                case ALERT_WARNING:  severity_str = "WARNING "; break;
                case ALERT_CRITICAL: severity_str = "CRITICAL"; break;
                default:             severity_str = "UNKNOWN "; break;
            }

            char time_str[64];
            struct tm *tm_info = localtime(&alert->timestamp);
            strftime(time_str, sizeof(time_str), "%Y-%m-%d %H:%M:%S", tm_info);

            printf("[%s] %s - %s\n", severity_str, time_str, alert->message);
        }
    }

    printf("\n================================================================================\n");
}
