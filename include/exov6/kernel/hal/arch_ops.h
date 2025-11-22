#ifndef HAL_ARCH_OPS_H
#define HAL_ARCH_OPS_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

// Narrow Interface for Architecture-Specific Operations

// Interrupt Control
void arch_irq_enter(void);
void arch_irq_exit(void);
void arch_irq_enable(void);
void arch_irq_disable(void);
bool arch_irq_enabled(void);

// Context Switching
struct arch_context;
void arch_switch_to(struct arch_context* prev, struct arch_context* next);

// TLB Management
void arch_tlb_flush_all(void);
void arch_tlb_flush_range(void* start, size_t size);
void arch_tlb_flush_page(void* addr);

// Timekeeping
uint64_t arch_get_cycles(void);

// Memory Barriers
void arch_barrier_full(void);
void arch_barrier_read(void);
void arch_barrier_write(void);

// CPU Management
uint32_t arch_cpu_id(void);
void arch_cpu_relax(void);
void arch_cpu_halt(void);

#endif // HAL_ARCH_OPS_H
