#pragma once
#define T_SYSCALL 64

// Trap vectors
#define T_IRQ0          32      // IRQ 0 corresponds to int T_IRQ0

// IRQ definitions
#define IRQ_TIMER        0
#define IRQ_KBD          1
#define IRQ_CASCADE      2
#define IRQ_COM2         3
#define IRQ_COM1         4
#define IRQ_IDE         14
#define IRQ_ERROR       19
#define IRQ_SPURIOUS    31

// Performance counter transfer trap
#define T_PCTR_TRANSFER 100
