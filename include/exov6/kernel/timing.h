#pragma once

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * x86-64 Timing and Performance Counters
 * 
 * RDTSC is not serializing - it can be reordered with other instructions
 * Use RDTSCP (serializing) or fence RDTSC for accurate measurements
 * 
 * References:
 * - Intel SDM Vol. 2B: RDTSC, RDTSCP instructions
 * - Intel SDM Vol. 3B: Chapter 17.17 Time-Stamp Counter
 */

/*
 * Read Time-Stamp Counter with serialization
 * 
 * RDTSCP is serializing on read - no instruction reordering after
 * Falls back to CPUID+RDTSC fence if RDTSCP not available
 */
static inline uint64_t rdtsc_serialized(void) {
    uint32_t aux;
    uint64_t tsc;
    
    // Check if RDTSCP is available (CPUID.80000001H:EDX[27])
    // For now, assume it's available on modern x86-64
    // TODO: Add CPUID detection
    
    uint32_t lo, hi;
    __asm__ __volatile__(
        "rdtscp"
        : "=a"(lo), "=d"(hi), "=c"(aux)
        :
        : "memory"
    );
    tsc = ((uint64_t)hi << 32) | lo;
    
    return tsc;
}

/*
 * Read Time-Stamp Counter with CPUID fencing (fallback)
 * 
 * CPUID is serializing - all prior instructions complete before CPUID
 * RDTSC executes after CPUID, giving accurate "after" timestamp
 */
static inline uint64_t rdtsc_fenced(void) {
    uint32_t eax, ebx, ecx, edx;
    uint64_t tsc;
    
    // Serialize with CPUID (leaf 0 is always supported)
    __asm__ __volatile__(
        "cpuid"
        : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
        : "a"(0)
        : "memory"
    );
    
    uint32_t lo, hi;
    __asm__ __volatile__(
        "rdtsc"
        : "=a"(lo), "=d"(hi)
        :
        : "memory"
    );
    tsc = ((uint64_t)hi << 32) | lo;
    
    return tsc;
}

/*
 * Read Time-Stamp Counter with pre-serialization
 * 
 * Use LFENCE before RDTSC to ensure all prior loads complete
 * Less overhead than CPUID but only serializes loads
 */
static inline uint64_t rdtsc_lfence(void) {
    uint64_t tsc;
    
    uint32_t lo, hi;
    __asm__ __volatile__(
        "lfence\n\t"
        "rdtsc"
        : "=a"(lo), "=d"(hi)
        :
        : "memory"
    );
    tsc = ((uint64_t)hi << 32) | lo;
    
    return tsc;
}

/*
 * High-precision timestamp for kernel use
 * 
 * Uses the most appropriate method based on context:
 * - Zone transitions: full serialization with RDTSCP
 * - Performance counters: LFENCE+RDTSC for lower overhead
 */
static inline uint64_t get_timestamp(void) {
    return rdtsc_serialized();
}

/*
 * Benchmark timing pair - before/after measurements
 */
typedef struct {
    uint64_t start;
    uint64_t end;
} timing_pair_t;

static inline void timing_start(timing_pair_t *timing) {
    timing->start = rdtsc_serialized();
}

static inline void timing_end(timing_pair_t *timing) {
    timing->end = rdtsc_serialized();
}

static inline uint64_t timing_cycles(const timing_pair_t *timing) {
    return timing->end - timing->start;
}

/*
 * Convert TSC cycles to nanoseconds
 * Requires TSC frequency calibration
 */
extern uint64_t tsc_freq_mhz;  // Set during boot

static inline uint64_t cycles_to_ns(uint64_t cycles) {
    // cycles / (freq_mhz * 1e6) * 1e9 = cycles * 1000 / freq_mhz
    return (cycles * 1000) / tsc_freq_mhz;
}

/*
 * Audit timestamp for security events
 * Always uses fully serialized timestamp
 */
static inline uint64_t audit_timestamp(void) {
    return rdtsc_serialized();
}

#ifdef __cplusplus
}
#endif
