#pragma once

/**
 * @file trapframe.h
 * @brief Unified trapframe definition for x86_64 architecture
 * 
 * Pure C17 implementation of processor state saved during interrupts/exceptions.
 * This structure captures the complete CPU state when transitioning from user
 * to kernel mode or during interrupt handling.
 */

#include <stdint.h>

// Only define if not already defined in arch_x86_64.h
#ifndef TRAPFRAME_DEFINED
#define TRAPFRAME_DEFINED

#ifdef __x86_64__

/**
 * x86_64 trap frame structure
 * 
 * When an interrupt/exception occurs, the CPU automatically pushes:
 * - SS, RSP, RFLAGS, CS, RIP (and error code for some exceptions)
 * 
 * The kernel then saves additional registers to preserve complete state.
 */
struct trapframe {
    // Segment registers (preserved by kernel)
    uint64_t ds;
    uint64_t es;
    uint64_t fs;
    uint64_t gs;
    
    // General purpose registers (preserved by kernel)
    uint64_t rax;
    uint64_t rbx;
    uint64_t rcx;
    uint64_t rdx;
    uint64_t rsi;
    uint64_t rdi;
    uint64_t rbp;
    uint64_t r8;
    uint64_t r9;
    uint64_t r10;
    uint64_t r11;
    uint64_t r12;
    uint64_t r13;
    uint64_t r14;
    uint64_t r15;
    
    // Trap number and error code
    uint64_t trapno;
    uint64_t err;
    
    // These are pushed by CPU automatically
    uint64_t rip;     // Instruction pointer
    uint64_t cs;      // Code segment
    uint64_t rflags;  // CPU flags
    uint64_t rsp;     // Stack pointer
    uint64_t ss;      // Stack segment
} __attribute__((packed));

#elif defined(__i386__)

/**
 * x86 (32-bit) trap frame structure
 */
struct trapframe {
    // Segment registers
    uint16_t gs;
    uint16_t padding1;
    uint16_t fs;
    uint16_t padding2;
    uint16_t es;
    uint16_t padding3;
    uint16_t ds;
    uint16_t padding4;
    
    // General purpose registers (as pushed by pusha)
    uint32_t edi;
    uint32_t esi;
    uint32_t ebp;
    uint32_t oesp;    // Original ESP (ignored)
    uint32_t ebx;
    uint32_t edx;
    uint32_t ecx;
    uint32_t eax;
    
    // Trap number and error code
    uint32_t trapno;
    uint32_t err;
    
    // Pushed by CPU automatically
    uint32_t eip;
    uint16_t cs;
    uint16_t padding5;
    uint32_t eflags;
    
    // Only pushed on privilege level change
    uint32_t esp;
    uint16_t ss;
    uint16_t padding6;
} __attribute__((packed));

#elif defined(__aarch64__)

/**
 * ARM64 exception frame structure
 */
struct trapframe {
    // General purpose registers x0-x30
    uint64_t x[31];
    
    // Stack pointer
    uint64_t sp;
    
    // Program counter (return address)
    uint64_t pc;
    
    // Processor state
    uint64_t pstate;
    
    // Exception syndrome register
    uint64_t esr;
    
    // Fault address register
    uint64_t far;
} __attribute__((packed));

#else
#error "Unsupported architecture for trapframe"
#endif

// Helper functions for trapframe manipulation
static inline void trapframe_init(struct trapframe *tf) {
    __builtin_memset(tf, 0, sizeof(*tf));
}

#ifdef __x86_64__
static inline uint64_t trapframe_get_pc(const struct trapframe *tf) {
    return tf->rip;
}

static inline void trapframe_set_pc(struct trapframe *tf, uint64_t pc) {
    tf->rip = pc;
}

static inline uint64_t trapframe_get_sp(const struct trapframe *tf) {
    return tf->rsp;
}

static inline void trapframe_set_sp(struct trapframe *tf, uint64_t sp) {
    tf->rsp = sp;
}
#elif defined(__i386__)
static inline uint32_t trapframe_get_pc(const struct trapframe *tf) {
    return tf->eip;
}

static inline void trapframe_set_pc(struct trapframe *tf, uint32_t pc) {
    tf->eip = pc;
}

static inline uint32_t trapframe_get_sp(const struct trapframe *tf) {
    return tf->esp;
}

static inline void trapframe_set_sp(struct trapframe *tf, uint32_t sp) {
    tf->esp = sp;
}
#elif defined(__aarch64__)
static inline uint64_t trapframe_get_pc(const struct trapframe *tf) {
    return tf->pc;
}

static inline void trapframe_set_pc(struct trapframe *tf, uint64_t pc) {
    tf->pc = pc;
}

static inline uint64_t trapframe_get_sp(const struct trapframe *tf) {
    return tf->sp;
}

static inline void trapframe_set_sp(struct trapframe *tf, uint64_t sp) {
    tf->sp = sp;
}
#endif

#endif // TRAPFRAME_DEFINED
