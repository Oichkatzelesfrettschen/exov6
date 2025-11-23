#pragma once

#include "param.h"
#include "mmu.h"
#include <arch_x86_64.h>
#include "exo_lock.h"  /* Modern lock subsystem - include BEFORE spinlock.h */
#include "spinlock.h"
#include "ipc.h"
#include "exo.h"
#include <exov6_interface.h>

// Context used for kernel context switches.
#ifndef CONTEXT_T_DEFINED
#define CONTEXT_T_DEFINED
#if defined(__x86_64__) || defined(__aarch64__)
typedef struct context64 context_t;
#else
typedef struct context context_t;
#endif
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

  // Unified lock system support (struct mcs_node defined in exo_lock.h)
  // Note: mcs_nodes are now allocated globally per-CPU in kernel/sync/qspinlock.c
  // This field is kept for compatibility but deprecated
  // struct mcs_node mcs_node;  // DEPRECATED - use global mcs_nodes[] array
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

#if defined(__aarch64__)
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
  struct proc *next_wait;        // Next process in sleeplock wait queue
  struct mailbox *mailbox;       // Per-process IPC mailbox
  struct proc *rq_next;          // Run queue next pointer
  struct proc *rq_prev;          // Run queue previous pointer
  
  label_t label;                 // Lattice Security Label (ExoV6)

  /* Process exit and IPC state */
  int exit_status;               /* Exit status for wait() */
  void *ipc_chan;                /* IPC channel for communication */

#ifdef USE_DAG_CHECKING
  /* DAG lock ordering tracker (Phase 4-6) */
  struct thread_lock_tracker lock_tracker;
#endif
};

// Ensure scheduler relies on fixed struct proc size
#if defined(__x86_64__) || defined(__aarch64__)
#ifdef USE_DAG_CHECKING
_Static_assert(sizeof(struct proc) <= 2048, "struct proc size too large");  // Updated for DAG tracker (with stats)
#else
_Static_assert(sizeof(struct proc) <= 512, "struct proc size incorrect");  // Updated for ExoV6 fields
#endif
#else
_Static_assert(sizeof(struct proc) <= 256, "struct proc size incorrect");  // Updated for ExoV6 fields
#endif


// Process memory is laid out contiguously, low addresses first:
//   text
//   original data and bss
//   fixed-size stack
//   expandable heap

struct ptable {
  struct spinlock lock;
  struct proc proc[NPROC];
};
