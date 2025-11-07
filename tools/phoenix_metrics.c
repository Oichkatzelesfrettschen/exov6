#define _POSIX_C_SOURCE 200809L
#include "phoenix_metrics.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>

static uint64_t simd_instr_count = 0;
static uint64_t scalar_fallback_count = 0;
static uint64_t ipc_latency_total = 0;
static uint64_t ipc_samples = 0;
static uint64_t ctx_switch_total = 0;
static uint64_t ctx_switch_samples = 0;
static uint64_t tmp_start = 0;

static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ull + ts.tv_nsec;
}

void phoenix_metrics_record_simd(uint64_t c) { simd_instr_count += c; }
void phoenix_metrics_record_scalar(uint64_t c) { scalar_fallback_count += c; }

void phoenix_metrics_record_ipc_start(void) { tmp_start = now_ns(); }
void phoenix_metrics_record_ipc_end(void) {
    uint64_t end = now_ns();
    if (end > tmp_start) {
        ipc_latency_total += end - tmp_start;
        ipc_samples++;
    }
}

void phoenix_metrics_record_ctx_switch_start(void) { tmp_start = now_ns(); }
void phoenix_metrics_record_ctx_switch_end(void) {
    uint64_t end = now_ns();
    if (end > tmp_start) {
        ctx_switch_total += end - tmp_start;
        ctx_switch_samples++;
    }
}

uint64_t phoenix_metrics_get_simd_count(void) { return simd_instr_count; }
uint64_t phoenix_metrics_get_scalar_count(void) { return scalar_fallback_count; }
uint64_t phoenix_metrics_get_ipc_latency(void) {
    return ipc_samples ? ipc_latency_total / ipc_samples : 0;
}
uint64_t phoenix_metrics_get_ctx_switch(void) {
    return ctx_switch_samples ? ctx_switch_total / ctx_switch_samples : 0;
}

void phoenix_metrics_reset(void) {
    simd_instr_count = 0;
    scalar_fallback_count = 0;
    ipc_latency_total = 0;
    ipc_samples = 0;
    ctx_switch_total = 0;
    ctx_switch_samples = 0;
    tmp_start = 0;
}

static void benchmark_variant(const char *name) {
    printf("-- %s --\n", name);
    char cmd[256];
    snprintf(cmd, sizeof(cmd), "make -C tests/microbench run > /dev/null");
    uint64_t start = now_ns();
    int r = system(cmd);
    uint64_t end = now_ns();
    if (r != 0)
        printf("benchmark failed\n");
    else
        printf("elapsed_ns:%llu\n", (unsigned long long)(end - start));
}

void benchmark_all_architectures(void) {
    DIR *d = opendir("build/isa");
    if (!d) {
        perror("opendir build/isa");
        return;
    }
    struct dirent *ent;
    while ((ent = readdir(d))) {
        if (ent->d_name[0] == '.')
            continue;
        char path[256];
        snprintf(path, sizeof(path), "build/isa/%s", ent->d_name);
        struct stat st;
        if (stat(path, &st) < 0 || !S_ISDIR(st.st_mode))
            continue;
        benchmark_variant(ent->d_name);
    }
    closedir(d);
}

#ifdef PHOENIX_METRICS_MAIN
int main(void) {
    benchmark_all_architectures();
    return 0;
}
#endif
