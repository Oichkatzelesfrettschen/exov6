#pragma once

static inline void cpu_relax(void) { __asm__ volatile("yield" ::: "memory"); }
