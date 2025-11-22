#pragma once
#include "q16_fixed.h"
typedef union {
    q16_t v[8];
    struct { q16_t e0, e1, e2, e3, e4, e5, e6, e7; };
    struct {
        q16_t cpu, memory, io_bandwidth, network_bandwidth, gpu_time, disk_quota, irq_count, capability_count;
    };
} resource_vector_t;
