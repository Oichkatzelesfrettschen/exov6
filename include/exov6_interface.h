// include/exov6_interface.h

#ifndef EXOV6_INTERFACE_H
#define EXOV6_INTERFACE_H

#ifdef __KERNEL__
#include <types.h>
#else
#include <stdint.h>
#endif

// --- Kernel Constants ---
#define EXO_MAX_ENV     64      // Max environments (processes)
#define EXO_PAGE_SIZE   4096    // Fixed page size

// --- Lattice Security Labels (Placeholder for Phase 2) ---
typedef uint32_t label_t;
#define LABEL_LOW       0x0
#define LABEL_HIGH      0x1

// --- System Call Numbers ---
// We replace the standard xv6 syscall numbers with these primitives.

// 1. Environment (Process) Control
#define SYS_env_create  1   // Create a new, blank environment (no memory yet)
#define SYS_env_run     2   // Yield CPU to a specific env (Scheduler Activation)
#define SYS_env_destroy 3   // Kill an environment

// 2. Memory Management (The Heart of Exokernel)
#define SYS_page_alloc  4   // Allocate a physical page
#define SYS_page_map    5   // Map a physical page to a virtual addr in an Env
#define SYS_page_unmap  6   // Unmap a page
#define SYS_page_stat   7   // Query status/owner of a physical page

// 3. IPC & Lattice Control
#define SYS_ipc_send    8   // Send a small message (register passing) to Env
#define SYS_ipc_recv    9   // Blocking receive
#define SYS_set_label   10  // (Privileged) Set the security label of a resource

// 4. Hardware IO (Capabilities)
#define SYS_disk_io     11  // Read/Write raw block (checked against capability)

// --- The Trap Frame Contract ---
// When we upcall into the LibOS, we pass this struct so the LibOS
// knows why it woke up (e.g., page fault, timer interrupt).
struct ExoTrapFrame {
    uint32_t trap_type;   // Page Fault, Timer, External IRQ
    uint32_t fault_addr;  // CR2 register equivalent
    uint32_t registers[8]; // Basic GP registers
};

#endif // EXOV6_INTERFACE_H
