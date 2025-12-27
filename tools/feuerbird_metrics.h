#pragma once
#ifndef FEUERBIRD_METRICS_H
#define FEUERBIRD_METRICS_H

#include <stdint.h>
#include <stdio.h>
#ifdef __cplusplus
extern "C" {
#endif

void feuerbird_metrics_record_simd(uint64_t count);
void feuerbird_metrics_record_scalar(uint64_t count);

void feuerbird_metrics_record_ipc_start(void);
void feuerbird_metrics_record_ipc_end(void);

void feuerbird_metrics_record_ctx_switch_start(void);
void feuerbird_metrics_record_ctx_switch_end(void);

uint64_t feuerbird_metrics_get_simd_count(void);
uint64_t feuerbird_metrics_get_scalar_count(void);
uint64_t feuerbird_metrics_get_ipc_latency(void);
uint64_t feuerbird_metrics_get_ctx_switch(void);

void feuerbird_metrics_reset(void);
void benchmark_all_architectures(void);

#ifdef __cplusplus
}
#endif

#endif /* FEUERBIRD_METRICS_H */
