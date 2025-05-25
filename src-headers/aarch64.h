#pragma once

#ifdef __cplusplus
extern "C" {
#endif
static inline void cpu_relax(void) { asm volatile("yield" ::: "memory"); }
#ifdef __cplusplus
}
#endif
