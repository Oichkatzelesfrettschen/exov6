#pragma once

#include "param.h"
#include "mmu.h"
#include "x86.h"
#include "spinlock.h"

// Context used for kernel context switches.
#ifdef __x86_64__
struct context64;
typedef struct context64 context_t;
#else
struct context;
typedef struct context context_t;
#endif

// Per-CPU state
struct cpu {
  uchar apicid;                // Local APIC ID
  context_t *scheduler;        // swtch() here to enter scheduler
  struct taskstate ts;         // Used by x86 to find stack for interrupt
  struct segdesc gdt[NSEGS];   // x86 global descriptor table
  volatile uint started;       // Has the CPU started?
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
  uint edi;
  uint esi;
  uint ebx;
  uint ebp;
  uint eip;
};
// Check that context saved by swtch.S matches this layout (5 registers)
_Static_assert(sizeof(struct context) == 20, "struct context size incorrect");

#ifdef __x86_64__
struct context64 {
  unsigned long r15;
  unsigned long r14;
  unsigned long r13;
  unsigned long r12;
  unsigned long rbx;
  unsigned long rbp;
  unsigned long rip;
};
#endif


enum procstate { UNUSED, EMBRYO, SLEEPING, RUNNABLE, RUNNING, ZOMBIE };

// Per-process state
struct proc {
  size_t sz;                     // Size of process memory (bytes)
  pde_t* pgdir;                // Page table
  char *kstack;                // Bottom of kernel stack for this process
  enum procstate state;        // Process state
  int pid;                     // Process ID
  struct proc *parent;         // Parent process
  struct trapframe *tf;        // Trap frame for current syscall
  context_t *context;          // swtch() here to run process
  void (*timer_upcall)(void);  // user-mode timer interrupt handler
  void *chan;                  // If non-zero, sleeping on chan
  int killed;                  // If non-zero, have been killed
  struct file *ofile[NOFILE];  // Open files
  struct inode *cwd;           // Current directory
  char name[16];               // Process name (debugging)
  uint pctr_cap;               // Capability for exo_pctr_transfer
  volatile uint pctr_signal;   // Signal counter for exo_pctr_transfer
};

// Ensure scheduler and utilities rely on fixed proc size (124 bytes)
#ifdef __x86_64__
_Static_assert(sizeof(struct proc) == 240, "struct proc size incorrect");
#else
_Static_assert(sizeof(struct proc) == 136, "struct proc size incorrect");
#endif
// Ensure scheduler and utilities rely on fixed proc size (136 bytes)
_Static_assert(sizeof(struct proc) == 136, "struct proc size incorrect");


// Process memory is laid out contiguously, low addresses first:
//   text
//   original data and bss
//   fixed-size stack
//   expandable heap

struct ptable {
  struct spinlock lock;
  struct proc proc[NPROC];
};
