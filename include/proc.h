#pragma once

#include "param.h"
#include "mmu.h"
#include <arch.h>
#include "spinlock.h"
#include "ipc.h"
#include "exo.h"
#include <sys/types.h>  // For uid_t, gid_t

// Context used for kernel context switches.
#if defined(__x86_64__) || defined(__aarch64__)
struct context64;
typedef struct context64 context_t;
#else
struct context;
typedef struct context context_t;
#endif

// Per-CPU state
struct cpu {
  uint8_t apicid;                // Local APIC ID
  context_t *scheduler;        // swtch() here to enter scheduler
#ifndef __aarch64__
  struct taskstate ts;         // Used by x86 to find stack for interrupt
  struct segdesc gdt[NSEGS];   // x86 global descriptor table
#endif
  volatile uint32_t started;       // Has the CPU started?
  int ncli;                    // Depth of pushcli nesting.
  int intena;                  // Were interrupts enabled before pushcli?
  struct proc *proc;           // The process running on this cpu or null
};

extern struct cpu cpus[NCPU];
extern int ncpu;

//PAGEBREAK: 17
// Saved registers for kernel context switches.
// Don't need to save all the segment registers (%cs, etc),
// because they are constant across kernel contexts.
// Don't need to save %eax, %ecx, %edx, because the
// x86 convention is that the caller has saved them.
// Contexts are stored at the bottom of the stack they
// describe; the stack pointer is the address of the context.
// The layout of the context matches the layout of the stack in swtch.S
// at the "Switch stacks" comment. Switch doesn't save eip explicitly,
// but it is on the stack and allocproc() manipulates it.
struct context {
  uint32_t edi;
  uint32_t esi;
  uint32_t ebx;
  uint32_t ebp;
  uint32_t eip;
};
// Check that context saved by swtch.S matches this layout (5 registers)
_Static_assert(sizeof(struct context) == 20, "struct context size incorrect");

#if defined(__x86_64__)
struct context64 {
  unsigned long r15;
  unsigned long r14;
  unsigned long r13;
  unsigned long r12;
  unsigned long rbx;
  unsigned long rbp;
  unsigned long rip;
};
#elif defined(__aarch64__)
struct context64 {
  unsigned long x19;
  unsigned long x20;
  unsigned long x21;
  unsigned long x22;
  unsigned long x23;
  unsigned long x24;
  unsigned long x25;
  unsigned long x26;
  unsigned long x27;
  unsigned long x28;
  unsigned long fp;
  unsigned long lr;
};
#endif


enum procstate { UNUSED, EMBRYO, SLEEPING, RUNNABLE, RUNNING, ZOMBIE };

// Simple mailbox queue used for IPC.
#define MAILBOX_BUFSZ 64

struct ipc_entry {
  zipc_msg_t msg;
  exo_cap frame;
};

struct mailbox {
  struct spinlock lock;
  struct ipc_entry buf[MAILBOX_BUFSZ];
  uint32_t r;
  uint32_t w;
  int inited;
};

// Per-process state
struct proc {
  size_t sz;                     // Size of process memory (bytes)
  pde_t* pgdir;                  // Page table
  char *kstack;                  // Bottom of kernel stack for this process
  enum procstate state;          // Process state
  int pid;                       // Process ID
  int pgid;                      // Process group ID (for signals)
  uid_t uid;                     // User ID (for POSIX compatibility)
  gid_t gid;                     // Group ID (for POSIX compatibility)
  int ngroups;                   // Number of supplementary groups
  gid_t groups[32];              // Supplementary group IDs (NGROUPS_MAX)
  struct proc *parent;           // Parent process
  struct trapframe *tf;          // Trap frame for current syscall
  context_t *context;            // swtch() here to run process
  void (*timer_upcall)(void);    // user-mode timer interrupt handler
  void *chan;                    // If non-zero, sleeping on chan
  int killed;                    // If non-zero, have been killed
  int pending_signal;            // Simple signal bitmask
  struct file *ofile[NOFILE];    // Open files
  struct inode *cwd;             // Current directory
  char name[16];                 // Process name (debugging)
  uint32_t pctr_cap;                 // Capability for exo_pctr_transfer
  volatile uint32_t pctr_signal;     // Signal counter for exo_pctr_transfer
  uint64_t gas_remaining;          // Remaining CPU budget
  int preferred_node;            // NUMA allocation preference
  int out_of_gas;                // Flag set when gas runs out
  struct mailbox *mailbox;       // Per-process IPC mailbox
  struct proc *rq_next;          // Run queue next pointer
  struct proc *rq_prev;          // Run queue previous pointer
  
  /* Signal handling state */
  struct signal_state {
    uint64_t pending;            /* Pending signals bitmap */
    uint64_t blocked;            /* Blocked signals mask */
    void (*handlers[64])(int);   /* Signal handlers */
    void *rtqueue;               /* Real-time signal queue */
    struct spinlock lock;
  } signal_state;
  
  /* FPU/SSE state */
  uint8_t fpu_state[512] __attribute__((aligned(16)));  /* FXSAVE area */
  int fpu_state_saved;           /* FPU state is saved */
  
  /* OS brand for virtualization */
  int brand;                     /* OS personality (BRAND_*) */
};

// Size will be recalculated after stabilization
// Previous size: 424 bytes on 64-bit, 168 on 32-bit
// Added signal_state and FPU state for POSIX compliance


// Process memory is laid out contiguously, low addresses first:
//   text
//   original data and bss
//   fixed-size stack
//   expandable heap

struct ptable {
  struct spinlock lock;
  struct proc proc[NPROC];
};
