#pragma once
#include <stdint.h>

struct libos_timer {
    uint64_t ticks;
};

uint64_t libos_timer_now(void);
