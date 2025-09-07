/*
 * cpu.c - x86_64 CPU HAL Implementation
 * 
 * Pure C17 implementation with minimal inline assembly
 * Provides complete CPU abstraction for x86_64 architecture
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdatomic.h>
#include <string.h>
#include "hal/hal.h"

/* x86_64 specific includes */
#include "arch/x86_64.h"
#include "types.h"

/* ============================================================================
 * x86_64 CPU Registers and Flags
 * ============================================================================ */

/* RFLAGS register bits */
#define X86_RFLAGS_CF    (1UL << 0)   /* Carry Flag */
#define X86_RFLAGS_PF    (1UL << 2)   /* Parity Flag */
#define X86_RFLAGS_AF    (1UL << 4)   /* Auxiliary Flag */
#define X86_RFLAGS_ZF    (1UL << 6)   /* Zero Flag */
#define X86_RFLAGS_SF    (1UL << 7)   /* Sign Flag */
#define X86_RFLAGS_TF    (1UL << 8)   /* Trap Flag */
#define X86_RFLAGS_IF    (1UL << 9)   /* Interrupt Enable Flag */
#define X86_RFLAGS_DF    (1UL << 10)  /* Direction Flag */
#define X86_RFLAGS_OF    (1UL << 11)  /* Overflow Flag */
#define X86_RFLAGS_IOPL  (3UL << 12)  /* I/O Privilege Level */
#define X86_RFLAGS_NT    (1UL << 14)  /* Nested Task */
#define X86_RFLAGS_RF    (1UL << 16)  /* Resume Flag */
#define X86_RFLAGS_VM    (1UL << 17)  /* Virtual-8086 Mode */
#define X86_RFLAGS_AC    (1UL << 18)  /* Alignment Check */
#define X86_RFLAGS_VIF   (1UL << 19)  /* Virtual Interrupt Flag */
#define X86_RFLAGS_VIP   (1UL << 20)  /* Virtual Interrupt Pending */
#define X86_RFLAGS_ID    (1UL << 21)  /* ID Flag */

/* MSR registers */
#define MSR_IA32_APIC_BASE       0x0000001B
#define MSR_IA32_TSC             0x00000010
#define MSR_IA32_MISC_ENABLE     0x000001A0
#define MSR_IA32_ENERGY_PERF_BIAS 0x000001B0

/* ============================================================================
 * CPU Detection and Information
 * ============================================================================ */

/* CPUID information structure */
typedef struct {
    uint32_t max_basic_cpuid;
    uint32_t max_extended_cpuid;
    char vendor[13];
    char brand[49];
    uint32_t family;
    uint32_t model;
    uint32_t stepping;
    uint32_t features_ecx;
    uint32_t features_edx;
    uint32_t cache_line_size;
    uint32_t logical_processors;
} x86_cpu_info_t;

static x86_cpu_info_t cpu_info;
static _Atomic(uint32_t) cpu_count = 1;

/* Execute CPUID instruction */
static inline void cpuid(uint32_t leaf, uint32_t subleaf,
                         uint32_t *eax, uint32_t *ebx, 
                         uint32_t *ecx, uint32_t *edx) {
    __asm__ __volatile__(
        "cpuid"
        : "=a"(*eax), "=b"(*ebx), "=c"(*ecx), "=d"(*edx)
        : "a"(leaf), "c"(subleaf)
    );
}

/* Initialize CPU information */
static void x86_cpu_detect(void) {
    uint32_t eax, ebx, ecx, edx;
    
    /* Get maximum CPUID leaf */
    cpuid(0, 0, &eax, &ebx, &ecx, &edx);
    cpu_info.max_basic_cpuid = eax;
    
    /* Get vendor string */
    memcpy(&cpu_info.vendor[0], &ebx, 4);
    memcpy(&cpu_info.vendor[4], &edx, 4);
    memcpy(&cpu_info.vendor[8], &ecx, 4);
    cpu_info.vendor[12] = '\0';
    
    /* Get CPU features */
    if (cpu_info.max_basic_cpuid >= 1) {
        cpuid(1, 0, &eax, &ebx, &ecx, &edx);
        
        cpu_info.stepping = eax & 0xF;
        cpu_info.model = (eax >> 4) & 0xF;
        cpu_info.family = (eax >> 8) & 0xF;
        
        if (cpu_info.family == 0xF) {
            cpu_info.family += (eax >> 20) & 0xFF;
        }
        if (cpu_info.family >= 6) {
            cpu_info.model += ((eax >> 16) & 0xF) << 4;
        }
        
        cpu_info.features_ecx = ecx;
        cpu_info.features_edx = edx;
        cpu_info.cache_line_size = ((ebx >> 8) & 0xFF) * 8;
        cpu_info.logical_processors = (ebx >> 16) & 0xFF;
    }
    
    /* Get brand string */
    cpuid(0x80000000, 0, &eax, &ebx, &ecx, &edx);
    cpu_info.max_extended_cpuid = eax;
    
    if (cpu_info.max_extended_cpuid >= 0x80000004) {
        uint32_t *brand = (uint32_t*)cpu_info.brand;
        for (uint32_t i = 0; i < 3; i++) {
            cpuid(0x80000002 + i, 0, &eax, &ebx, &ecx, &edx);
            brand[i*4 + 0] = eax;
            brand[i*4 + 1] = ebx;
            brand[i*4 + 2] = ecx;
            brand[i*4 + 3] = edx;
        }
        cpu_info.brand[48] = '\0';
    }
}

/* ============================================================================
 * Context Switching Implementation
 * ============================================================================ */

/* Save CPU context - pure C17 with minimal assembly */
static void x86_context_save(hal_cpu_context_t *ctx) {
    if (!ctx) return;
    
    /* Save general purpose registers using inline assembly */
    __asm__ __volatile__(
        "movq %%rax, %0\n\t"
        "movq %%rbx, %1\n\t"
        "movq %%rcx, %2\n\t"
        "movq %%rdx, %3\n\t"
        "movq %%rsi, %4\n\t"
        "movq %%rdi, %5\n\t"
        "movq %%rbp, %6\n\t"
        "movq %%r8,  %7\n\t"
        "movq %%r9,  %8\n\t"
        "movq %%r10, %9\n\t"
        "movq %%r11, %10\n\t"
        "movq %%r12, %11\n\t"
        "movq %%r13, %12\n\t"
        "movq %%r14, %13\n\t"
        "movq %%r15, %14\n\t"
        : "=m"(ctx->registers[0]), "=m"(ctx->registers[1]),
          "=m"(ctx->registers[2]), "=m"(ctx->registers[3]),
          "=m"(ctx->registers[4]), "=m"(ctx->registers[5]),
          "=m"(ctx->registers[6]), "=m"(ctx->registers[8]),
          "=m"(ctx->registers[9]), "=m"(ctx->registers[10]),
          "=m"(ctx->registers[11]), "=m"(ctx->registers[12]),
          "=m"(ctx->registers[13]), "=m"(ctx->registers[14]),
          "=m"(ctx->registers[15])
        :
        : "memory"
    );
    
    /* Save stack pointer and instruction pointer */
    __asm__ __volatile__(
        "movq %%rsp, %0\n\t"
        "leaq 1f(%%rip), %1\n\t"
        "1:\n\t"
        : "=m"(ctx->sp), "=r"(ctx->pc)
        :
        : "memory"
    );
    
    /* Save RFLAGS */
    __asm__ __volatile__(
        "pushfq\n\t"
        "popq %0"
        : "=r"(ctx->flags)
        :
        : "memory"
    );
    
    /* Save FPU/SSE state if needed */
    __asm__ __volatile__(
        "fxsave64 %0"
        : "=m"(ctx->fp_state[0])
        :
        : "memory"
    );
}

/* Restore CPU context */
static void x86_context_restore(const hal_cpu_context_t *ctx) {
    if (!ctx) return;
    
    /* Restore FPU/SSE state */
    __asm__ __volatile__(
        "fxrstor64 %0"
        :
        : "m"(ctx->fp_state[0])
        : "memory"
    );
    
    /* Restore RFLAGS */
    __asm__ __volatile__(
        "pushq %0\n\t"
        "popfq"
        :
        : "r"(ctx->flags)
        : "memory", "cc"
    );
    
    /* Restore general purpose registers and jump */
    __asm__ __volatile__(
        "movq %0,  %%rax\n\t"
        "movq %1,  %%rbx\n\t"
        "movq %2,  %%rcx\n\t"
        "movq %3,  %%rdx\n\t"
        "movq %4,  %%rsi\n\t"
        "movq %5,  %%rdi\n\t"
        "movq %6,  %%rbp\n\t"
        "movq %7,  %%r8\n\t"
        "movq %8,  %%r9\n\t"
        "movq %9,  %%r10\n\t"
        "movq %10, %%r11\n\t"
        "movq %11, %%r12\n\t"
        "movq %12, %%r13\n\t"
        "movq %13, %%r14\n\t"
        "movq %14, %%r15\n\t"
        "movq %15, %%rsp\n\t"
        "jmpq *%16"
        :
        : "m"(ctx->registers[0]), "m"(ctx->registers[1]),
          "m"(ctx->registers[2]), "m"(ctx->registers[3]),
          "m"(ctx->registers[4]), "m"(ctx->registers[5]),
          "m"(ctx->registers[6]), "m"(ctx->registers[8]),
          "m"(ctx->registers[9]), "m"(ctx->registers[10]),
          "m"(ctx->registers[11]), "m"(ctx->registers[12]),
          "m"(ctx->registers[13]), "m"(ctx->registers[14]),
          "m"(ctx->registers[15]), "m"(ctx->sp), "r"(ctx->pc)
    );
}

/* Context switch between two contexts */
static void x86_context_switch(hal_cpu_context_t *from, hal_cpu_context_t *to) {
    if (!from || !to) return;
    
    x86_context_save(from);
    x86_context_restore(to);
}

/* ============================================================================
 * Interrupt Management
 * ============================================================================ */

/* Check if interrupts are enabled */
static bool x86_interrupts_enabled(void) {
    uint64_t flags;
    __asm__ __volatile__(
        "pushfq\n\t"
        "popq %0"
        : "=r"(flags)
        :
        : "memory"
    );
    return (flags & X86_RFLAGS_IF) != 0;
}

/* Enable interrupts */
static void x86_interrupts_enable(void) {
    __asm__ __volatile__("sti" ::: "memory");
}

/* Disable interrupts */
static void x86_interrupts_disable(void) {
    __asm__ __volatile__("cli" ::: "memory");
}

/* Save interrupt state and disable */
static uint64_t x86_interrupts_save(void) {
    uint64_t flags;
    __asm__ __volatile__(
        "pushfq\n\t"
        "popq %0\n\t"
        "cli"
        : "=r"(flags)
        :
        : "memory"
    );
    return flags;
}

/* Restore interrupt state */
static void x86_interrupts_restore(uint64_t flags) {
    if (flags & X86_RFLAGS_IF) {
        x86_interrupts_enable();
    }
}

/* ============================================================================
 * CPU Identification
 * ============================================================================ */

/* Get current CPU ID */
static uint32_t x86_get_cpu_id(void) {
    uint32_t apic_id;
    uint32_t eax, ebx, ecx, edx;
    
    /* Get APIC ID from CPUID */
    cpuid(1, 0, &eax, &ebx, &ecx, &edx);
    apic_id = (ebx >> 24) & 0xFF;
    
    return apic_id;
}

/* Get CPU count */
static uint32_t x86_get_cpu_count(void) {
    return atomic_load_explicit(&cpu_count, memory_order_acquire);
}

/* Get CPU information string */
static void x86_get_cpu_info(char *buffer, size_t size) {
    if (!buffer || size == 0) return;
    
    snprintf(buffer, size, 
             "CPU: %s\n"
             "Vendor: %s\n"
             "Family: %u, Model: %u, Stepping: %u\n"
             "Cache Line: %u bytes\n"
             "Logical CPUs: %u\n",
             cpu_info.brand,
             cpu_info.vendor,
             cpu_info.family, cpu_info.model, cpu_info.stepping,
             cpu_info.cache_line_size,
             cpu_info.logical_processors);
}

/* ============================================================================
 * Cache Operations
 * ============================================================================ */

/* Flush cache line(s) */
static void x86_cache_flush(void *addr, size_t size) {
    uint8_t *p = (uint8_t*)addr;
    uint8_t *end = p + size;
    
    /* CLFLUSH instruction flushes cache lines */
    for (; p < end; p += cpu_info.cache_line_size) {
        __asm__ __volatile__("clflush (%0)" : : "r"(p) : "memory");
    }
    
    /* Memory fence to ensure completion */
    __asm__ __volatile__("mfence" ::: "memory");
}

/* Invalidate cache line(s) */
static void x86_cache_invalidate(void *addr, size_t size) {
    /* On x86, we use CLFLUSH which both invalidates and flushes */
    x86_cache_flush(addr, size);
}

/* Flush entire cache */
static void x86_cache_flush_all(void) {
    /* WBINVD instruction writes back and invalidates entire cache */
    __asm__ __volatile__("wbinvd" ::: "memory");
}

/* ============================================================================
 * CPU Control
 * ============================================================================ */

/* CPU pause instruction for spin loops */
static void x86_cpu_pause(void) {
    __asm__ __volatile__("pause" ::: "memory");
}

/* Halt CPU until next interrupt */
static void x86_cpu_halt(void) {
    __asm__ __volatile__("hlt" ::: "memory");
}

/* Reset CPU */
static void x86_cpu_reset(void) {
    /* Triple fault to reset - create invalid IDT and trigger interrupt */
    struct {
        uint16_t limit;
        uint64_t base;
    } __attribute__((packed)) idtr = { 0, 0 };
    
    __asm__ __volatile__(
        "lidt %0\n\t"
        "int $3"
        :
        : "m"(idtr)
    );
}

/* ============================================================================
 * Time Stamp Counter
 * ============================================================================ */

/* Read time stamp counter */
static uint64_t x86_read_timestamp(void) {
    uint32_t low, high;
    __asm__ __volatile__(
        "rdtsc"
        : "=a"(low), "=d"(high)
        :
        : "memory"
    );
    return ((uint64_t)high << 32) | low;
}

/* Get TSC frequency (approximate) */
static uint64_t x86_timestamp_frequency(void) {
    /* This is platform-specific and should be calibrated */
    /* Default to 2.4 GHz for now */
    return 2400000000ULL;
}

/* ============================================================================
 * x86_64 CPU Operations Table
 * ============================================================================ */

static const hal_cpu_ops_t x86_cpu_ops = {
    .context_save = x86_context_save,
    .context_restore = x86_context_restore,
    .context_switch = x86_context_switch,
    
    .interrupts_enabled = x86_interrupts_enabled,
    .interrupts_enable = x86_interrupts_enable,
    .interrupts_disable = x86_interrupts_disable,
    .interrupts_save = x86_interrupts_save,
    .interrupts_restore = x86_interrupts_restore,
    
    .get_cpu_id = x86_get_cpu_id,
    .get_cpu_count = x86_get_cpu_count,
    .get_cpu_info = x86_get_cpu_info,
    
    .cache_flush = x86_cache_flush,
    .cache_invalidate = x86_cache_invalidate,
    .cache_flush_all = x86_cache_flush_all,
    
    .cpu_pause = x86_cpu_pause,
    .cpu_halt = x86_cpu_halt,
    .cpu_reset = x86_cpu_reset,
    
    .read_timestamp = x86_read_timestamp,
    .timestamp_frequency = x86_timestamp_frequency
};

/* ============================================================================
 * Initialization
 * ============================================================================ */

void x86_cpu_init(void) {
    /* Detect CPU features */
    x86_cpu_detect();
    
    /* Count available CPUs (this would involve ACPI/MP tables) */
    atomic_store_explicit(&cpu_count, cpu_info.logical_processors, 
                         memory_order_release);
}

/* Export operations table */
const hal_cpu_ops_t* x86_get_cpu_ops(void) {
    return &x86_cpu_ops;
}