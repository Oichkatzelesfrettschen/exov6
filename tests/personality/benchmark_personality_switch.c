/**
 * @file benchmark_personality_switch.c
 * @brief Performance benchmark for multi-personality syscall gateway
 * 
 * Measures overhead of personality detection, syscall routing,
 * and structure translation.
 */

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <unistd.h>
#include <sys/time.h>

// Include kernel headers
#include "../../kernel/sys/syscall_gateway.h"
#include "../../kernel/sys/abi_versioning.h"

// Benchmark configuration
#define ITERATIONS 1000000
#define WARMUP_ITERATIONS 10000

// Timing utilities
static inline uint64_t get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}

static inline uint64_t rdtsc(void) {
#ifdef __x86_64__
    uint32_t lo, hi;
    __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
#else
    return get_time_ns();
#endif
}

// Benchmark results
typedef struct {
    const char *name;
    uint64_t total_cycles;
    uint64_t min_cycles;
    uint64_t max_cycles;
    uint64_t avg_cycles;
    uint64_t total_ns;
    uint64_t avg_ns;
} benchmark_result_t;

/**
 * Benchmark native syscall dispatch
 */
benchmark_result_t benchmark_native_dispatch(void) {
    benchmark_result_t result = {
        .name = "Native FeuerBird dispatch",
        .min_cycles = UINT64_MAX,
        .max_cycles = 0,
        .total_cycles = 0
    };
    
    // Warmup
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        unsigned long nr = 20;  // getpid
        volatile unsigned int num = syscall_get_number(nr);
        (void)num;
    }
    
    // Benchmark
    uint64_t start_ns = get_time_ns();
    
    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc();
        
        unsigned long nr = 20;  // getpid
        volatile unsigned int num = syscall_get_number(nr);
        (void)num;
        
        uint64_t end = rdtsc();
        uint64_t cycles = end - start;
        
        result.total_cycles += cycles;
        if (cycles < result.min_cycles) result.min_cycles = cycles;
        if (cycles > result.max_cycles) result.max_cycles = cycles;
    }
    
    uint64_t end_ns = get_time_ns();
    
    result.total_ns = end_ns - start_ns;
    result.avg_cycles = result.total_cycles / ITERATIONS;
    result.avg_ns = result.total_ns / ITERATIONS;
    
    return result;
}

/**
 * Benchmark classed syscall dispatch
 */
benchmark_result_t benchmark_classed_dispatch(syscall_personality_t personality) {
    benchmark_result_t result = {
        .name = "Classed dispatch",
        .min_cycles = UINT64_MAX,
        .max_cycles = 0,
        .total_cycles = 0
    };
    
    // Warmup
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        unsigned long nr = syscall_make_classed(personality, 20);
        volatile unsigned int class = syscall_get_class(nr);
        volatile unsigned int num = syscall_get_number(nr);
        (void)class;
        (void)num;
    }
    
    // Benchmark
    uint64_t start_ns = get_time_ns();
    
    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc();
        
        unsigned long nr = syscall_make_classed(personality, 20);
        volatile unsigned int class = syscall_get_class(nr);
        volatile unsigned int num = syscall_get_number(nr);
        (void)class;
        (void)num;
        
        uint64_t end = rdtsc();
        uint64_t cycles = end - start;
        
        result.total_cycles += cycles;
        if (cycles < result.min_cycles) result.min_cycles = cycles;
        if (cycles > result.max_cycles) result.max_cycles = cycles;
    }
    
    uint64_t end_ns = get_time_ns();
    
    result.total_ns = end_ns - start_ns;
    result.avg_cycles = result.total_cycles / ITERATIONS;
    result.avg_ns = result.total_ns / ITERATIONS;
    
    return result;
}

/**
 * Benchmark structure translation
 */
benchmark_result_t benchmark_structure_translation(void) {
    benchmark_result_t result = {
        .name = "Structure translation (V6→Modern)",
        .min_cycles = UINT64_MAX,
        .max_cycles = 0,
        .total_cycles = 0
    };
    
    // Test structures
    struct stat_v6 v6_stat = {
        .st_dev = 0x0102,
        .st_ino = 0x1234,
        .st_mode = 0755,
        .st_nlink = 2,
        .st_uid = 100,
        .st_gid = 50,
        .st_size0 = 0x01,
        .st_size1 = 0x2345,
        .st_atime = {0x0000, 0x1234},
        .st_mtime = {0x0000, 0x5678}
    };
    
    struct stat modern_stat;
    
    // Warmup
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        translate_stat_version(&v6_stat, ABI_VERSION_V6,
                              &modern_stat, ABI_VERSION_POSIX24);
    }
    
    // Benchmark
    uint64_t start_ns = get_time_ns();
    
    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc();
        
        translate_stat_version(&v6_stat, ABI_VERSION_V6,
                              &modern_stat, ABI_VERSION_POSIX24);
        
        uint64_t end = rdtsc();
        uint64_t cycles = end - start;
        
        result.total_cycles += cycles;
        if (cycles < result.min_cycles) result.min_cycles = cycles;
        if (cycles > result.max_cycles) result.max_cycles = cycles;
    }
    
    uint64_t end_ns = get_time_ns();
    
    result.total_ns = end_ns - start_ns;
    result.avg_cycles = result.total_cycles / ITERATIONS;
    result.avg_ns = result.total_ns / ITERATIONS;
    
    return result;
}

/**
 * Benchmark errno translation
 */
benchmark_result_t benchmark_errno_translation(void) {
    benchmark_result_t result = {
        .name = "Errno translation",
        .min_cycles = UINT64_MAX,
        .max_cycles = 0,
        .total_cycles = 0
    };
    
    // Warmup
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        volatile int err = translate_errno_version(11, ABI_VERSION_V7, ABI_VERSION_LINUX6);
        (void)err;
    }
    
    // Benchmark
    uint64_t start_ns = get_time_ns();
    
    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc();
        
        volatile int err = translate_errno_version(11, ABI_VERSION_V7, ABI_VERSION_LINUX6);
        (void)err;
        
        uint64_t end = rdtsc();
        uint64_t cycles = end - start;
        
        result.total_cycles += cycles;
        if (cycles < result.min_cycles) result.min_cycles = cycles;
        if (cycles > result.max_cycles) result.max_cycles = cycles;
    }
    
    uint64_t end_ns = get_time_ns();
    
    result.total_ns = end_ns - start_ns;
    result.avg_cycles = result.total_cycles / ITERATIONS;
    result.avg_ns = result.total_ns / ITERATIONS;
    
    return result;
}

/**
 * Benchmark complete syscall flow
 */
benchmark_result_t benchmark_complete_flow(syscall_personality_t personality) {
    benchmark_result_t result = {
        .name = "Complete syscall flow",
        .min_cycles = UINT64_MAX,
        .max_cycles = 0,
        .total_cycles = 0
    };
    
    // Warmup
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        // Simulate complete flow
        unsigned long nr = syscall_make_classed(personality, 18);  // stat
        unsigned int class = syscall_get_class(nr);
        unsigned int num = syscall_get_number(nr);
        
        // Would trigger structure translation
        if (class == SYSCALL_CLASS_LINUX) {
            volatile int translated = 1;
            (void)translated;
        }
    }
    
    // Benchmark
    uint64_t start_ns = get_time_ns();
    
    for (int i = 0; i < ITERATIONS; i++) {
        uint64_t start = rdtsc();
        
        // Complete flow
        unsigned long nr = syscall_make_classed(personality, 18);
        unsigned int class = syscall_get_class(nr);
        unsigned int num = syscall_get_number(nr);
        
        // Simulate translation check
        if (class != SYSCALL_CLASS_FEUERBIRD) {
            volatile int needs_translation = 1;
            (void)needs_translation;
        }
        
        uint64_t end = rdtsc();
        uint64_t cycles = end - start;
        
        result.total_cycles += cycles;
        if (cycles < result.min_cycles) result.min_cycles = cycles;
        if (cycles > result.max_cycles) result.max_cycles = cycles;
    }
    
    uint64_t end_ns = get_time_ns();
    
    result.total_ns = end_ns - start_ns;
    result.avg_cycles = result.total_cycles / ITERATIONS;
    result.avg_ns = result.total_ns / ITERATIONS;
    
    return result;
}

/**
 * Print benchmark results
 */
void print_results(benchmark_result_t *results, int count) {
    printf("\n📊 Benchmark Results\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("%-35s │ Avg Cycles │ Min │ Max │ Avg ns\n", "Operation");
    printf("───────────────────────────────────┼────────────┼─────┼─────┼────────\n");
    
    for (int i = 0; i < count; i++) {
        printf("%-35s │ %10llu │ %4llu │ %4llu │ %6llu\n",
               results[i].name,
               results[i].avg_cycles,
               results[i].min_cycles,
               results[i].max_cycles,
               results[i].avg_ns);
    }
    
    printf("═══════════════════════════════════════════════════════════════\n");
}

/**
 * Calculate overhead percentages
 */
void calculate_overhead(benchmark_result_t *results, int count) {
    if (count < 2) return;
    
    uint64_t baseline = results[0].avg_cycles;  // Native dispatch
    
    printf("\n📈 Performance Overhead Analysis\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("Baseline: Native FeuerBird dispatch = %llu cycles\n\n", baseline);
    
    for (int i = 1; i < count; i++) {
        double overhead = ((double)(results[i].avg_cycles - baseline) / baseline) * 100.0;
        printf("%-35s: %+.2f%% overhead\n", results[i].name, overhead);
        
        if (overhead > 10.0) {
            printf("  ⚠️ WARNING: Exceeds 10%% target overhead!\n");
        } else if (overhead < 5.0) {
            printf("  ✅ Excellent: Under 5%% overhead\n");
        } else {
            printf("  ✓ Good: Within target range\n");
        }
    }
    
    printf("═══════════════════════════════════════════════════════════════\n");
}

int main(int argc, char *argv[]) {
    printf("⚡ Multi-Personality Syscall Gateway Performance Benchmark\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("Iterations: %d\n", ITERATIONS);
    printf("Warmup: %d\n", WARMUP_ITERATIONS);
    printf("\nRunning benchmarks...\n");
    
    benchmark_result_t results[10];
    int result_count = 0;
    
    // Native dispatch
    printf("  Benchmarking native dispatch...\n");
    results[result_count++] = benchmark_native_dispatch();
    
    // Linux personality
    printf("  Benchmarking Linux personality...\n");
    results[result_count++] = benchmark_classed_dispatch(SYSCALL_CLASS_LINUX);
    results[result_count - 1].name = "Linux personality dispatch";
    
    // BSD personality
    printf("  Benchmarking BSD personality...\n");
    results[result_count++] = benchmark_classed_dispatch(SYSCALL_CLASS_BSD);
    results[result_count - 1].name = "BSD personality dispatch";
    
    // Illumos personality
    printf("  Benchmarking Illumos personality...\n");
    results[result_count++] = benchmark_classed_dispatch(SYSCALL_CLASS_ILLUMOS);
    results[result_count - 1].name = "Illumos personality dispatch";
    
    // Structure translation
    printf("  Benchmarking structure translation...\n");
    results[result_count++] = benchmark_structure_translation();
    
    // Errno translation
    printf("  Benchmarking errno translation...\n");
    results[result_count++] = benchmark_errno_translation();
    
    // Complete flow
    printf("  Benchmarking complete Linux flow...\n");
    results[result_count++] = benchmark_complete_flow(SYSCALL_CLASS_LINUX);
    results[result_count - 1].name = "Complete Linux syscall flow";
    
    // Print results
    print_results(results, result_count);
    calculate_overhead(results, result_count);
    
    // Performance targets check
    printf("\n🎯 Performance Targets Check\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    
    int targets_met = 0;
    int total_targets = 3;
    
    // Check syscall dispatch < 100 cycles
    if (results[0].avg_cycles < 100) {
        printf("✅ Native dispatch < 100 cycles: %llu cycles\n", results[0].avg_cycles);
        targets_met++;
    } else {
        printf("❌ Native dispatch > 100 cycles: %llu cycles\n", results[0].avg_cycles);
    }
    
    // Check translation overhead < 10%
    double max_overhead = 0;
    for (int i = 1; i < result_count; i++) {
        double overhead = ((double)(results[i].avg_cycles - results[0].avg_cycles) / 
                          results[0].avg_cycles) * 100.0;
        if (overhead > max_overhead) max_overhead = overhead;
    }
    
    if (max_overhead < 10.0) {
        printf("✅ Max translation overhead < 10%%: %.2f%%\n", max_overhead);
        targets_met++;
    } else {
        printf("❌ Max translation overhead > 10%%: %.2f%%\n", max_overhead);
    }
    
    // Check structure translation < 500 cycles
    benchmark_result_t *struct_result = NULL;
    for (int i = 0; i < result_count; i++) {
        if (strstr(results[i].name, "Structure")) {
            struct_result = &results[i];
            break;
        }
    }
    
    if (struct_result && struct_result->avg_cycles < 500) {
        printf("✅ Structure translation < 500 cycles: %llu cycles\n", 
               struct_result->avg_cycles);
        targets_met++;
    } else if (struct_result) {
        printf("❌ Structure translation > 500 cycles: %llu cycles\n",
               struct_result->avg_cycles);
    }
    
    printf("\nTargets met: %d/%d\n", targets_met, total_targets);
    printf("═══════════════════════════════════════════════════════════════\n");
    
    if (targets_met == total_targets) {
        printf("\n🎉 All performance targets achieved!\n");
        printf("✅ Multi-personality gateway meets requirements!\n");
        return 0;
    } else {
        printf("\n⚠️ Some performance targets missed\n");
        printf("   Further optimization may be needed\n");
        return 1;
    }
}