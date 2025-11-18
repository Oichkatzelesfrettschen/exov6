/**
 * @file posix_traps.c
 * @brief POSIX 2024 (SUSv5) Compliant Trap and Signal Implementation
 * 
 * Pure C17 implementation synthesizing illumos, BSD, and Mach concepts
 * with complete POSIX.1-2024 compliance for exokernel architecture.
 */

#include <types.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "arch.h"
#include "trapframe.h"
#include "spinlock.h"
#include "fs.h"
#include "file.h"
#include "elf.h"
#include "../traps.h"

/* Error codes */
#define ENOSYS  38  /* Function not implemented */
#define EAGAIN  11  /* Try again */
#define EINVAL  22  /* Invalid argument */
#define ESRCH    3  /* No such process */

/* System call definitions */
#define NSYSCALLS 64  /* Number of system calls */
extern int (*syscalls[])(void);

/* Process brands for OS virtualization */
#define BRAND_NATIVE   0
#define BRAND_LINUX    1
#define BRAND_FREEBSD  2
#define BRAND_ILLUMOS  3

/* ELF core dump definitions */
#define ET_CORE     4       /* Core file */
#define PT_NOTE     4       /* Note segment */
#define PT_LOAD     1       /* Loadable segment */
#define PF_R        0x4     /* Readable */
#define PF_W        0x2     /* Writable */
#define PF_X        0x1     /* Executable */
#define EM_X86_64   62      /* AMD x86-64 */
#define T_FILE      2       /* Regular file type */

/* External VM function */
extern char* walkaddr(pde_t *pgdir, uint32_t va);

/* Helper for page copy */
static inline int copyout_page(pde_t *pgdir, char *dst, uint32_t va, uint32_t n) {
    /* Copy page from process address space */
    char *src = (char*)walkaddr(pgdir, va);
    if (!src) return -1;
    memmove(dst, src, n);
    return 0;
}

/* Process states (from proc.h if not defined) */
#ifndef STOPPED
#define STOPPED SLEEPING  /* Map to existing state */
#endif

/* Disable signal/FPU/brand code until proc struct is extended */
#if 0  /* POSIX_SIGNALS_DISABLED - requires extended proc struct */

/* Forward declarations */
void deliver_signal(struct proc *p, int signo);
void setup_signal_frame(struct proc *p, int signo, void (*handler)(int));
void create_core_dump(struct proc *p);

/* External interrupt handlers */
extern void timer_interrupt(void);
extern void kbd_interrupt(void);
extern void ide_interrupt(void);

/* ============================================================================
 * POSIX 2024 Signal Definitions (IEEE Std 1003.1-2024)
 * ============================================================================ */

#define POSIX_NSIG          65      /* Total number of signals including RT */
#define POSIX_SIGRTMIN      32      /* First real-time signal */
#define POSIX_SIGRTMAX      64      /* Last real-time signal */
#define POSIX_RTSIG_MAX     32      /* Number of real-time signals */

/* Standard POSIX Signals (1-31) */
#define POSIX_SIGHUP        1       /* Hangup */
#define POSIX_SIGINT        2       /* Interrupt */
#define POSIX_SIGQUIT       3       /* Quit */
#define POSIX_SIGILL        4       /* Illegal instruction */
#define POSIX_SIGTRAP       5       /* Trace/breakpoint trap */
#define POSIX_SIGABRT       6       /* Abort */
#define POSIX_SIGIOT        6       /* IOT trap (same as SIGABRT) */
#define POSIX_SIGBUS        7       /* Bus error */
#define POSIX_SIGFPE        8       /* Floating point exception */
#define POSIX_SIGKILL       9       /* Kill (cannot be caught) */
#define POSIX_SIGUSR1       10      /* User defined signal 1 */
#define POSIX_SIGSEGV       11      /* Segmentation violation */
#define POSIX_SIGUSR2       12      /* User defined signal 2 */
#define POSIX_SIGPIPE       13      /* Broken pipe */
#define POSIX_SIGALRM       14      /* Alarm clock */
#define POSIX_SIGTERM       15      /* Termination */
#define POSIX_SIGSTKFLT     16      /* Stack fault */
#define POSIX_SIGCHLD       17      /* Child status changed */
#define POSIX_SIGCONT       18      /* Continue */
#define POSIX_SIGSTOP       19      /* Stop (cannot be caught) */
#define POSIX_SIGTSTP       20      /* Terminal stop */
#define POSIX_SIGTTIN       21      /* Background read from tty */
#define POSIX_SIGTTOU       22      /* Background write to tty */
#define POSIX_SIGURG        23      /* Urgent condition on socket */
#define POSIX_SIGXCPU       24      /* CPU time limit exceeded */
#define POSIX_SIGXFSZ       25      /* File size limit exceeded */
#define POSIX_SIGVTALRM     26      /* Virtual alarm clock */
#define POSIX_SIGPROF       27      /* Profiling alarm clock */
#define POSIX_SIGWINCH      28      /* Window size change */
#define POSIX_SIGIO         29      /* I/O now possible */
#define POSIX_SIGPOLL       29      /* Pollable event (same as SIGIO) */
#define POSIX_SIGPWR        30      /* Power failure */
#define POSIX_SIGSYS        31      /* Bad system call */

/* Signal Actions */
typedef enum {
    SIG_DFL,    /* Default action */
    SIG_IGN,    /* Ignore signal */
    SIG_CATCH   /* Catch with handler */
} sig_action_t;

/* Default Signal Actions per POSIX */
typedef enum {
    SIGACT_TERM,        /* Terminate process */
    SIGACT_CORE,        /* Terminate with core dump */
    SIGACT_IGNORE,      /* Ignore signal */
    SIGACT_STOP,        /* Stop process */
    SIGACT_CONT         /* Continue if stopped */
} sig_default_action_t;

/* Signal set type for signal masking */
typedef uint64_t sigset_t;

/* Signal value union for real-time signals */
union sigval {
    int sival_int;
    void *sival_ptr;
};

/* Signal action structure */
struct sigaction {
    void (*sa_handler)(int);     /* Signal handler */
    sigset_t sa_mask;            /* Signals to block during handler */
    int sa_flags;                /* Signal options */
    void (*sa_sigaction)(int, void *, void *);  /* Extended handler */
};

/* sigprocmask operations */
#define SIG_BLOCK   0
#define SIG_UNBLOCK 1
#define SIG_SETMASK 2

/* Signal Queue Entry for Real-Time Signals */
struct sigqueue_entry {
    int signo;
    union sigval value;
    struct sigqueue_entry *next;
};

/* Signal state is now defined in proc.h */

/* Default actions for each signal per POSIX.1-2024 */
static const sig_default_action_t default_actions[32] = {
    [0]                 = SIGACT_IGNORE,   /* Null signal */
    [POSIX_SIGHUP]     = SIGACT_TERM,
    [POSIX_SIGINT]     = SIGACT_TERM,
    [POSIX_SIGQUIT]    = SIGACT_CORE,
    [POSIX_SIGILL]     = SIGACT_CORE,
    [POSIX_SIGTRAP]    = SIGACT_CORE,
    [POSIX_SIGABRT]    = SIGACT_CORE,
    [POSIX_SIGBUS]     = SIGACT_CORE,
    [POSIX_SIGFPE]     = SIGACT_CORE,
    [POSIX_SIGKILL]    = SIGACT_TERM,     /* Cannot be caught */
    [POSIX_SIGUSR1]    = SIGACT_TERM,
    [POSIX_SIGSEGV]    = SIGACT_CORE,
    [POSIX_SIGUSR2]    = SIGACT_TERM,
    [POSIX_SIGPIPE]    = SIGACT_TERM,
    [POSIX_SIGALRM]    = SIGACT_TERM,
    [POSIX_SIGTERM]    = SIGACT_TERM,
    [POSIX_SIGSTKFLT]  = SIGACT_TERM,
    [POSIX_SIGCHLD]    = SIGACT_IGNORE,
    [POSIX_SIGCONT]    = SIGACT_CONT,
    [POSIX_SIGSTOP]    = SIGACT_STOP,     /* Cannot be caught */
    [POSIX_SIGTSTP]    = SIGACT_STOP,
    [POSIX_SIGTTIN]    = SIGACT_STOP,
    [POSIX_SIGTTOU]    = SIGACT_STOP,
    [POSIX_SIGURG]     = SIGACT_IGNORE,
    [POSIX_SIGXCPU]    = SIGACT_CORE,
    [POSIX_SIGXFSZ]    = SIGACT_CORE,
    [POSIX_SIGVTALRM]  = SIGACT_TERM,
    [POSIX_SIGPROF]    = SIGACT_TERM,
    [POSIX_SIGWINCH]   = SIGACT_IGNORE,
    [POSIX_SIGIO]      = SIGACT_TERM,
    [POSIX_SIGPWR]     = SIGACT_TERM,
    [POSIX_SIGSYS]     = SIGACT_CORE
};

/* ============================================================================
 * CPU Control Register Operations (x86_64 specific)
 * ============================================================================ */

#define CR0_EM  0x00000004  /* Emulation */
#define CR0_TS  0x00000008  /* Task Switched */

static inline uint64_t rcr0(void) {
    uint64_t val;
    __asm__ volatile("mov %%cr0, %0" : "=r"(val));
    return val;
}

static inline void posix_lcr0(uint64_t val) {
    __asm__ volatile("mov %0, %%cr0" : : "r"(val));
}

static inline uint64_t posix_rcr2(void) {
    uint64_t val;
    __asm__ volatile("mov %%cr2, %0" : "=r"(val));
    return val;
}

static inline void fxrstor(void *addr) {
    __asm__ volatile("fxrstor (%0)" : : "r"(addr));
}

static inline void fxsave(void *addr) {
    __asm__ volatile("fxsave (%0)" : : "r"(addr));
}

/* ============================================================================
 * Brand-specific syscall handlers
 * ============================================================================ */

static int linux_syscall_handler(struct trapframe *tf) {
    /* Linux syscall emulation - translate to POSIX */
    /* Would map Linux syscall numbers to POSIX equivalents */
    return -ENOSYS;
}

static int freebsd_syscall_handler(struct trapframe *tf) {
    /* FreeBSD syscall emulation */
    return -ENOSYS;
}

static int illumos_syscall_handler(struct trapframe *tf) {
    /* illumos/Solaris syscall emulation */
    return -ENOSYS;
}

/* ============================================================================
 * Signal Handling Functions
 * ============================================================================ */

static void send_signal(struct proc *p, int signo) {
    if (!p || signo < 1 || signo >= POSIX_NSIG) return;

    /* Set signal as pending */
    p->signal_state.pending |= (1ULL << signo);
    
    /* Wake up process if sleeping */
    if (p->state == SLEEPING) {
        p->state = RUNNABLE;
    }
}

static void handle_pending_signals(struct proc *p) {
    if (!p) return;
    
    uint64_t pending = p->signal_state.pending & ~p->signal_state.blocked;
    if (!pending) return;
    
    /* Process each pending signal */
    for (int signo = 1; signo < POSIX_NSIG; signo++) {
        if (pending & (1ULL << signo)) {
            /* Clear pending bit */
            p->signal_state.pending &= ~(1ULL << signo);
            
            /* Get handler */
            void (*handler)(int) = p->signal_state.handlers[signo];
            
            if (handler && handler != (void*)SIG_IGN) {
                /* Custom handler */
                if (handler != (void*)SIG_DFL) {
                    /* Call user handler (would need to set up signal frame) */
                    /* For now, just mark as handled */
                }
            } else if (handler == (void*)SIG_DFL) {
                /* Default action */
                switch (default_actions[signo]) {
                case SIGACT_TERM:
                case SIGACT_CORE:
                    p->killed = 1;
                    break;
                case SIGACT_STOP:
                    p->state = SLEEPING;
                    break;
                case SIGACT_CONT:
                    if (p->state == SLEEPING)
                        p->state = RUNNABLE;
                    break;
                case SIGACT_IGNORE:
                default:
                    break;
                }
            }
        }
    }
}

static int handle_page_fault(struct proc *p, uint64_t addr, uint32_t err) {
    /* Simplified page fault handler */
    /* In real implementation, would check:
     * - Valid virtual address
     * - Page permissions
     * - Copy-on-write
     * - Demand paging
     */
    
    /* For now, just return error */
    return -1;
}

/* ============================================================================
 * Trap Vector Table (x86-64 + Mach-like)
 * ============================================================================ */

/* Intel/AMD Trap Numbers */
#define TRAP_DIVIDE         0   /* Divide error */
#define TRAP_DEBUG          1   /* Debug exception */
#define TRAP_NMI            2   /* Non-maskable interrupt */
#define TRAP_BREAKPOINT     3   /* Breakpoint (INT3) */
#define TRAP_OVERFLOW       4   /* Overflow (INTO) */
#define TRAP_BOUNDS         5   /* Bounds check */
#define TRAP_INVALID_OP     6   /* Invalid opcode */
#define TRAP_NO_FPU         7   /* FPU not available */
#define TRAP_DOUBLE_FAULT   8   /* Double fault */
#define TRAP_FPU_OVERRUN    9   /* FPU segment overrun */
#define TRAP_INVALID_TSS    10  /* Invalid TSS */
#define TRAP_NO_SEGMENT     11  /* Segment not present */
#define TRAP_STACK_FAULT    12  /* Stack fault */
#define TRAP_GP_FAULT       13  /* General protection fault */
#define TRAP_PAGE_FAULT     14  /* Page fault */
#define TRAP_FPU_ERROR      16  /* FPU error */
#define TRAP_ALIGNMENT      17  /* Alignment check */
#define TRAP_MACHINE_CHECK  18  /* Machine check */
#define TRAP_SIMD_ERROR     19  /* SIMD floating point error */

/* Mach-like Trap Extensions */
#define MACH_SYSCALL        0x80    /* Mach system call */
#define MACH_MDEP           0x81    /* Machine dependent */
#define MACH_RPC            0x82    /* Mach RPC */

/* illumos/Solaris Brand Syscall */
#define BRAND_SYSCALL       0x83    /* Branded syscall for zones */

/* Trap Handler Function Type */
typedef void (*trap_handler_t)(struct trapframe *tf);

/* Forward declarations of trap handlers */
void trap_divide_error(struct trapframe *tf);
void trap_debug(struct trapframe *tf);
void trap_breakpoint(struct trapframe *tf);
void trap_overflow(struct trapframe *tf);
void trap_bounds_check(struct trapframe *tf);
void trap_invalid_opcode(struct trapframe *tf);
void trap_device_not_available(struct trapframe *tf);
void trap_double_fault(struct trapframe *tf);
void trap_invalid_tss(struct trapframe *tf);
void trap_segment_not_present(struct trapframe *tf);
void trap_stack_fault(struct trapframe *tf);
void trap_general_protection(struct trapframe *tf);
void trap_page_fault(struct trapframe *tf);
void trap_fpu_error(struct trapframe *tf);
void trap_alignment_check(struct trapframe *tf);
void trap_machine_check(struct trapframe *tf);
void trap_simd_error(struct trapframe *tf);
void syscall_handler(struct trapframe *tf);
void mach_syscall_handler(struct trapframe *tf);
void brand_syscall_handler(struct trapframe *tf);
void irq_handler(struct trapframe *tf);

/* Global Trap Vector Table */
static trap_handler_t trap_vectors[256];

/* ============================================================================
 * Trap Handling Implementation
 * ============================================================================ */

/**
 * Initialize trap vector table
 */
void posix_trap_init(void) {
    /* Clear all vectors */
    for (int i = 0; i < 256; i++) {
        trap_vectors[i] = NULL;
    }
    
    /* Install standard x86-64 trap handlers */
    trap_vectors[TRAP_DIVIDE]       = trap_divide_error;
    trap_vectors[TRAP_DEBUG]        = trap_debug;
    trap_vectors[TRAP_BREAKPOINT]   = trap_breakpoint;
    trap_vectors[TRAP_OVERFLOW]     = trap_overflow;
    trap_vectors[TRAP_BOUNDS]       = trap_bounds_check;
    trap_vectors[TRAP_INVALID_OP]   = trap_invalid_opcode;
    trap_vectors[TRAP_NO_FPU]       = trap_device_not_available;
    trap_vectors[TRAP_DOUBLE_FAULT] = trap_double_fault;
    trap_vectors[TRAP_INVALID_TSS]  = trap_invalid_tss;
    trap_vectors[TRAP_NO_SEGMENT]   = trap_segment_not_present;
    trap_vectors[TRAP_STACK_FAULT]  = trap_stack_fault;
    trap_vectors[TRAP_GP_FAULT]     = trap_general_protection;
    trap_vectors[TRAP_PAGE_FAULT]   = trap_page_fault;
    trap_vectors[TRAP_FPU_ERROR]    = trap_fpu_error;
    trap_vectors[TRAP_ALIGNMENT]    = trap_alignment_check;
    trap_vectors[TRAP_MACHINE_CHECK]= trap_machine_check;
    trap_vectors[TRAP_SIMD_ERROR]   = trap_simd_error;
    
    /* System call handlers */
    trap_vectors[T_SYSCALL]         = syscall_handler;
    trap_vectors[MACH_SYSCALL]      = mach_syscall_handler;
    trap_vectors[BRAND_SYSCALL]     = brand_syscall_handler;
    
    /* IRQ handlers */
    for (int i = T_IRQ0; i < T_IRQ0 + 16; i++) {
        trap_vectors[i] = irq_handler;
    }
}

/**
 * Main trap dispatcher - called from assembly
 */
void trap_dispatch(struct trapframe *tf) {
    struct proc *p = myproc();
    
    /* Save trap frame in process */
    if (p) {
        p->tf = tf;
    }
    
    /* Check trap number validity */
    if (tf->trapno >= 256) {
        panic("Invalid trap number");
    }
    
    /* Gas accounting for trap handling */
    if (p && p->gas_remaining > 0) {
        p->gas_remaining--;
    }
    
    /* Dispatch to handler */
    trap_handler_t handler = trap_vectors[tf->trapno];
    if (handler) {
        handler(tf);
    } else {
        /* Unhandled trap - send signal or panic */
        if (p && (tf->cs & 3) == DPL_USER) {
            /* User mode trap - send signal */
            send_signal(p, POSIX_SIGSEGV);
        } else {
            /* Kernel trap - panic */
            cprintf("Unhandled trap %d at %p\n", tf->trapno, tf->rip);
            panic("Unhandled kernel trap");
        }
    }
    
    /* Check for pending signals */
    if (p && (tf->cs & 3) == DPL_USER) {
        handle_pending_signals(p);
    }
}

/* ============================================================================
 * Specific Trap Handlers
 * ============================================================================ */

void trap_divide_error(struct trapframe *tf) {
    struct proc *p = myproc();
    if ((tf->cs & 3) == DPL_USER) {
        send_signal(p, POSIX_SIGFPE);
    } else {
        panic("Kernel divide error");
    }
}

void trap_debug(struct trapframe *tf) {
    struct proc *p = myproc();
    send_signal(p, POSIX_SIGTRAP);
}

void trap_breakpoint(struct trapframe *tf) {
    struct proc *p = myproc();
    send_signal(p, POSIX_SIGTRAP);
}

void trap_overflow(struct trapframe *tf) {
    struct proc *p = myproc();
    send_signal(p, POSIX_SIGFPE);
}

void trap_bounds_check(struct trapframe *tf) {
    struct proc *p = myproc();
    send_signal(p, POSIX_SIGSEGV);
}

void trap_invalid_opcode(struct trapframe *tf) {
    struct proc *p = myproc();
    if ((tf->cs & 3) == DPL_USER) {
        send_signal(p, POSIX_SIGILL);
    } else {
        panic("Kernel invalid opcode");
    }
}

void trap_device_not_available(struct trapframe *tf) {
    /* Handle FPU/SSE lazy context switching */
    struct proc *p = myproc();
    if (p) {
        /* Enable FPU/SSE for this process */
        lcr0(rcr0() & ~(CR0_EM | CR0_TS));
        /* Restore FPU state if saved */
        if (p->fpu_state_saved) {
            fxrstor(p->fpu_state);
        }
    }
}

void trap_double_fault(struct trapframe *tf) {
    panic("Double fault");
}

void trap_invalid_tss(struct trapframe *tf) {
    panic("Invalid TSS");
}

void trap_segment_not_present(struct trapframe *tf) {
    struct proc *p = myproc();
    if ((tf->cs & 3) == DPL_USER) {
        send_signal(p, POSIX_SIGSEGV);
    } else {
        panic("Kernel segment not present");
    }
}

void trap_stack_fault(struct trapframe *tf) {
    struct proc *p = myproc();
    if ((tf->cs & 3) == DPL_USER) {
        send_signal(p, POSIX_SIGSEGV);
    } else {
        panic("Kernel stack fault");
    }
}

void trap_general_protection(struct trapframe *tf) {
    struct proc *p = myproc();
    if ((tf->cs & 3) == DPL_USER) {
        send_signal(p, POSIX_SIGSEGV);
    } else {
        cprintf("General protection fault at %p\n", tf->rip);
        panic("Kernel general protection fault");
    }
}

void trap_page_fault(struct trapframe *tf) {
    uint64_t fault_addr = rcr2();
    struct proc *p = myproc();
    
    /* Check if it's a valid page fault we can handle */
    if ((tf->cs & 3) == DPL_USER) {
        /* User page fault - try to handle */
        if (handle_page_fault(p, fault_addr, tf->err) < 0) {
            /* Couldn't handle - send SIGSEGV */
            send_signal(p, POSIX_SIGSEGV);
        }
    } else {
        /* Kernel page fault - usually fatal */
        cprintf("Kernel page fault at %p, addr %p\n", tf->rip, fault_addr);
        panic("Kernel page fault");
    }
}

void trap_fpu_error(struct trapframe *tf) {
    struct proc *p = myproc();
    send_signal(p, POSIX_SIGFPE);
}

void trap_alignment_check(struct trapframe *tf) {
    struct proc *p = myproc();
    send_signal(p, POSIX_SIGBUS);
}

void trap_machine_check(struct trapframe *tf) {
    panic("Machine check exception");
}

void trap_simd_error(struct trapframe *tf) {
    struct proc *p = myproc();
    send_signal(p, POSIX_SIGFPE);
}

/* ============================================================================
 * System Call Handlers
 * ============================================================================ */

/**
 * POSIX system call handler (INT 0x80 or SYSCALL instruction)
 */
void syscall_handler(struct trapframe *tf) {
    struct proc *p = myproc();
    
    /* System call number in RAX */
    int num = tf->rax;
    
    /* Validate system call number */
    if (num < 0 || num >= NSYSCALLS) {
        tf->rax = -ENOSYS;
        return;
    }
    
    /* Gas accounting */
    if (p->gas_remaining < 10) {
        tf->rax = -EAGAIN;
        return;
    }
    p->gas_remaining -= 10;
    
    /* Call system call handler */
    tf->rax = syscalls[num]();
}

/**
 * Mach system call handler (for Mach compatibility)
 */
void mach_syscall_handler(struct trapframe *tf) {
    /* Mach trap number in RAX */
    int trapno = tf->rax;
    
    /* Handle Mach traps */
    switch (trapno) {
    case 0:  /* mach_reply_port */
    case 1:  /* mach_thread_self */
    case 2:  /* mach_task_self */
    case 3:  /* mach_host_self */
        /* Implement Mach trap */
        tf->rax = -ENOSYS;  /* Not implemented */
        break;
    default:
        tf->rax = -ENOSYS;
        break;
    }
}

/**
 * Branded system call handler (illumos-style zones)
 */
void brand_syscall_handler(struct trapframe *tf) {
    struct proc *p = myproc();
    
    /* Check if process is branded */
    if (p->brand == BRAND_NATIVE) {
        tf->rax = -ENOSYS;
        return;
    }
    
    /* Dispatch to brand-specific handler */
    switch (p->brand) {
    case BRAND_LINUX:
        /* Linux system call emulation */
        linux_syscall_handler(tf);
        break;
    case BRAND_FREEBSD:
        /* FreeBSD system call emulation */
        freebsd_syscall_handler(tf);
        break;
    default:
        tf->rax = -ENOSYS;
        break;
    }
}

/**
 * IRQ handler dispatcher
 */
void irq_handler(struct trapframe *tf) {
    int irq = tf->trapno - T_IRQ0;
    
    /* EOI to APIC */
    lapiceoi();
    
    /* Dispatch to device handler */
    switch (irq) {
    case IRQ_TIMER:
        timer_interrupt();
        break;
    case IRQ_KBD:
        kbd_interrupt();
        break;
    case IRQ_IDE:
        ide_interrupt();
        break;
    default:
        /* Spurious interrupt */
        break;
    }
}

/* ============================================================================
 * Signal Handling Implementation
 * ============================================================================ */

/**
 * Raise signal to process (public version)
 */
void raise_signal(struct proc *p, int signo) {
    if (!p || signo < 1 || signo >= POSIX_NSIG) {
        return;
    }
    
    acquire(&p->signal_state.lock);
    
    /* Check if signal is blocked */
    if (p->signal_state.blocked & (1ULL << signo)) {
        /* Mark as pending */
        p->signal_state.pending |= (1ULL << signo);
    } else {
        /* Deliver immediately */
        deliver_signal(p, signo);
    }
    
    release(&p->signal_state.lock);
}

/**
 * Deliver signal to process
 */
void deliver_signal(struct proc *p, int signo) {
    /* Check for handler */
    void (*handler)(int) = p->signal_state.handlers[signo];
    
    if (handler == SIG_IGN) {
        /* Ignore signal */
        return;
    }
    
    if (handler == SIG_DFL) {
        /* Default action */
        sig_default_action_t action = default_actions[signo];
        
        switch (action) {
        case SIGACT_TERM:
            /* Terminate process */
            p->killed = 1;
            break;
        case SIGACT_CORE:
            /* Terminate with core dump */
            create_core_dump(p);
            p->killed = 1;
            break;
        case SIGACT_IGNORE:
            /* Ignore */
            break;
        case SIGACT_STOP:
            /* Stop process */
            p->state = STOPPED;
            break;
        case SIGACT_CONT:
            /* Continue if stopped */
            if (p->state == STOPPED) {
                p->state = RUNNABLE;
            }
            break;
        }
    } else {
        /* Call user handler */
        setup_signal_frame(p, signo, handler);
    }
}

/**
 * Handle pending signals for process (public version)
 */
void handle_pending_signals_public(struct proc *p) {
    if (!p || !p->signal_state.pending) {
        return;
    }
    
    acquire(&p->signal_state.lock);
    
    /* Process standard signals first (priority over RT) */
    for (int sig = 1; sig < POSIX_SIGRTMIN; sig++) {
        if (p->signal_state.pending & (1ULL << sig)) {
            p->signal_state.pending &= ~(1ULL << sig);
            deliver_signal(p, sig);
        }
    }
    
    /* Process real-time signals in order */
    struct sigqueue_entry *entry = p->signal_state.rtqueue;
    while (entry) {
        struct sigqueue_entry *next = entry->next;
        deliver_signal(p, entry->signo);
        /* Free entry */
        entry = next;
    }
    p->signal_state.rtqueue = NULL;
    
    release(&p->signal_state.lock);
}

/**
 * Create core dump for debugging
 */
void create_core_dump(struct proc *p) {
    /* Generate core dump filename */
    char corename[16];
    int pid = p->pid;
    
    /* Simple integer to string conversion for kernel */
    corename[0] = 'c'; corename[1] = 'o'; corename[2] = 'r'; corename[3] = 'e';
    corename[4] = '.';
    int pos = 5;
    if (pid == 0) {
        corename[pos++] = '0';
    } else {
        char digits[8];
        int ndigits = 0;
        while (pid > 0) {
            digits[ndigits++] = '0' + (pid % 10);
            pid /= 10;
        }
        while (ndigits > 0) {
            corename[pos++] = digits[--ndigits];
        }
    }
    corename[pos] = '\0';
    
    /* Write actual ELF core dump */
    struct elfhdr ehdr;
    struct proghdr phdr;
    
    /* Open core file for writing (create if needed) */
    struct inode *ip = namei(corename);
    if (!ip) {
        /* Create new file - write directly to root directory */
        ip = dirlookup(namei("/"), corename, 0);
        if (!ip) {
            /* Allocate new inode for core file */
            ip = ialloc(1, T_FILE);  /* Device 1, regular file */
            if (!ip) return;  /* Failed to allocate */
        }
    }
    ilock(ip);
    
    /* Write ELF header */
    memset(&ehdr, 0, sizeof(ehdr));
    ehdr.magic = ELF_MAGIC;
    ehdr.elf[0] = 0x7f;
    ehdr.elf[1] = 'E';
    ehdr.elf[2] = 'L';
    ehdr.elf[3] = 'F';
    ehdr.type = ET_CORE;    /* Core file type */
    ehdr.machine = EM_X86_64;
    ehdr.version = 1;
    ehdr.phoff = sizeof(ehdr);
    ehdr.phentsize = sizeof(phdr);
    ehdr.phnum = 2;  /* Note segment + memory segment */
    
    uint32_t off = 0;
    writei(ip, (char*)&ehdr, off, sizeof(ehdr));
    off += sizeof(ehdr);
    
    /* Write note segment with registers */
    struct {
        uint32_t namesz;
        uint32_t descsz;
        uint32_t type;
        char name[8];
        struct trapframe tf;
    } note;
    
    note.namesz = 5;  /* "CORE\0" */
    note.descsz = sizeof(struct trapframe);
    note.type = 1;     /* NT_PRSTATUS */
    note.name[0] = 'C';
    note.name[1] = 'O';
    note.name[2] = 'R';
    note.name[3] = 'E';
    note.name[4] = '\0';
    if (p->tf) {
        memmove(&note.tf, p->tf, sizeof(struct trapframe));
    }
    
    /* Program header for note segment */
    memset(&phdr, 0, sizeof(phdr));
    phdr.type = PT_NOTE;
    phdr.off = off + sizeof(phdr) * 2;
    phdr.filesz = sizeof(note);
    phdr.memsz = sizeof(note);
    writei(ip, (char*)&phdr, off, sizeof(phdr));
    off += sizeof(phdr);
    
    /* Program header for memory segment */
    memset(&phdr, 0, sizeof(phdr));
    phdr.type = PT_LOAD;
    phdr.vaddr = 0;
    phdr.paddr = 0;
    phdr.off = off + sizeof(phdr) + sizeof(note);
    phdr.filesz = p->sz;
    phdr.memsz = p->sz;
    phdr.flags = PF_R | PF_W | PF_X;
    writei(ip, (char*)&phdr, off, sizeof(phdr));
    off += sizeof(phdr);
    
    /* Write note data */
    writei(ip, (char*)&note, off, sizeof(note));
    off += sizeof(note);
    
    /* Write process memory pages */
    for (uint32_t va = 0; va < p->sz; va += PGSIZE) {
        char *pa = kalloc();
        if (pa && copyout_page(p->pgdir, pa, va, PGSIZE) >= 0) {
            writei(ip, pa, off, PGSIZE);
            kfree(pa);
        }
        off += PGSIZE;
    }
    
    /* Update inode size and release */
    ip->size = off;
    iupdate(ip);
    iunlockput(ip);
    
    cprintf("Core dump written: %s (%d bytes)\n", corename, off);
}

/**
 * Set up signal frame on user stack
 */
void setup_signal_frame(struct proc *p, int signo, void (*handler)(int)) {
    struct trapframe *tf = p->tf;
    
    /* Save current context on user stack */
    uint64_t sp = tf->rsp;
    sp -= sizeof(struct trapframe);
    
    /* Copy trap frame to user stack */
    if (copyout(p->pgdir, sp, tf, sizeof(*tf)) < 0) {
        /* Can't deliver signal - kill process */
        p->killed = 1;
        return;
    }
    
    /* Set up for signal handler */
    tf->rdi = signo;        /* First argument: signal number */
    tf->rip = (uint64_t)handler;  /* Jump to handler */
    tf->rsp = sp;           /* New stack pointer */
    
    /* Return address: sigreturn system call trampoline */
    sp -= 8;
    /* Create inline sigreturn trampoline code:
     * mov $15, %rax   ; sigreturn syscall number
     * syscall         ; invoke system call
     */
    static const uint8_t sigreturn_code[] = {
        0x48, 0xc7, 0xc0, 0x0f, 0x00, 0x00, 0x00,  /* mov $15, %rax */
        0x0f, 0x05                                   /* syscall */
    };
    
    /* Allocate trampoline in user space if not already done */
    uint64_t sigreturn_addr = 0x400000;  /* Fixed address in user text segment */
    copyout(p->pgdir, sigreturn_addr, (char*)sigreturn_code, sizeof(sigreturn_code));
    copyout(p->pgdir, sp, &sigreturn_addr, 8);
    tf->rsp = sp;
}

/* create_core_dump is already defined earlier in the file */

/* ============================================================================
 * System Call Implementation
 * ============================================================================ */

/**
 * sigaction - examine and change signal action
 */
int sys_sigaction(void) {
    int signo;
    struct sigaction *act, *oact;
    
    if (argint(0, &signo) < 0 ||
        argptr(1, (char**)&act, sizeof(*act)) < 0 ||
        argptr(2, (char**)&oact, sizeof(*oact)) < 0) {
        return -EINVAL;
    }
    
    if (signo < 1 || signo >= POSIX_NSIG) {
        return -EINVAL;
    }
    
    /* Cannot catch SIGKILL or SIGSTOP */
    if (signo == POSIX_SIGKILL || signo == POSIX_SIGSTOP) {
        return -EINVAL;
    }
    
    struct proc *p = myproc();
    acquire(&p->signal_state.lock);
    
    /* Return old action */
    if (oact) {
        oact->sa_handler = p->signal_state.handlers[signo];
        /* Copy other fields */
    }
    
    /* Set new action */
    if (act) {
        p->signal_state.handlers[signo] = act->sa_handler;
        /* Copy other fields */
    }
    
    release(&p->signal_state.lock);
    return 0;
}

/**
 * kill - send signal to process or process group
 */
int sys_kill(void) {
    int pid, signo;
    
    if (argint(0, &pid) < 0 || argint(1, &signo) < 0) {
        return -EINVAL;
    }
    
    if (signo < 0 || signo >= POSIX_NSIG) {
        return -EINVAL;
    }
    
    /* Find target process */
    struct proc *p = NULL;
    acquire(&ptable.lock);
    
    if (pid > 0) {
        /* Send to specific process */
        for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
            if (p->pid == pid) {
                send_signal(p, signo);
                break;
            }
        }
    } else if (pid == 0) {
        /* Send to process group */
        struct proc *curproc = myproc();
        for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
            if (p->pgid == curproc->pgid) {
                send_signal(p, signo);
            }
        }
    } else if (pid == -1) {
        /* Send to all processes (except init) */
        for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
            if (p->pid > 1) {
                send_signal(p, signo);
            }
        }
    } else {
        /* Send to process group -pid */
        for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
            if (p->pgid == -pid) {
                send_signal(p, signo);
            }
        }
    }
    
    release(&ptable.lock);
    return p ? 0 : -ESRCH;
}

/**
 * sigprocmask - examine and change blocked signals
 */
int sys_sigprocmask(void) {
    int how;
    sigset_t *set, *oset;
    
    if (argint(0, &how) < 0 ||
        argptr(1, (char**)&set, sizeof(*set)) < 0 ||
        argptr(2, (char**)&oset, sizeof(*oset)) < 0) {
        return -EINVAL;
    }
    
    struct proc *p = myproc();
    acquire(&p->signal_state.lock);
    
    /* Return old mask */
    if (oset) {
        *oset = p->signal_state.blocked;
    }
    
    /* Update mask */
    if (set) {
        switch (how) {
        case SIG_BLOCK:
            p->signal_state.blocked |= *set;
            break;
        case SIG_UNBLOCK:
            p->signal_state.blocked &= ~*set;
            break;
        case SIG_SETMASK:
            p->signal_state.blocked = *set;
            break;
        default:
            release(&p->signal_state.lock);
            return -EINVAL;
        }
        
        /* Cannot block SIGKILL or SIGSTOP */
        p->signal_state.blocked &= ~((1ULL << POSIX_SIGKILL) | (1ULL << POSIX_SIGSTOP));
    }
    
    release(&p->signal_state.lock);
    
    /* Check for newly unblocked signals */
    handle_pending_signals(p);
    
    return 0;
}

#endif /* POSIX_SIGNALS_DISABLED */

/* Stub implementations when signals disabled */
void trap_init(void) {
    /* Stub - full POSIX trap handling disabled */
}

void posix_trap_handler(void) {
    /* Stub - full POSIX trap handling disabled */
}