#pragma once
#include <stdint.h>
#include <stdio.h>
#ifdef __cplusplus
extern "C" {
#endif

void phoenix_metrics_record_simd(uint64_t count);
void phoenix_metrics_record_scalar(uint64_t count);

void phoenix_metrics_record_ipc_start(void);
void phoenix_metrics_record_ipc_end(void);

void phoenix_metrics_record_ctx_switch_start(void);
void phoenix_metrics_record_ctx_switch_end(void);

uint64_t phoenix_metrics_get_simd_count(void);
uint64_t phoenix_metrics_get_scalar_count(void);
uint64_t phoenix_metrics_get_ipc_latency(void);
uint64_t phoenix_metrics_get_ctx_switch(void);

void phoenix_metrics_reset(void);
void benchmark_all_architectures(void);

#ifdef __cplusplus
}
#endif
