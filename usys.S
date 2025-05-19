# usys.S - User System Call Interface

This assembly file defines the system call interface for user programs in the ExoKernel operating system. It provides assembly stubs that translate user-space function calls into kernel system calls.

## Architecture Support
- **x86 (32-bit)**: Uses `int $T_SYSCALL` instruction with parameters in `%eax`
- **x86_64 (64-bit)**: Uses `syscall` instruction with parameters in `%rax`

## System Call Categories

### Standard POSIX System Calls
- Process management: `fork`, `exit`, `wait`, `getpid`, `exec`, `kill`
- File operations: `open`, `close`, `read`, `write`, `fstat`, `link`, `unlink`
- Directory operations: `mkdir`, `chdir`, `mknod`
- Memory management: `sbrk`
- I/O operations: `pipe`, `dup`
- Time operations: `sleep`, `uptime`

### ExoKernel-Specific System Calls
- Memory management: `mappte`, `exo_unbind_page`, `exo_alloc_block`, `exo_bind_block`
- Process control: `exo_yield_to`, `proc_alloc`
- I/O operations: `exo_read_disk`, `exo_write_disk`, `exo_flush_block`
- Communication: `exo_send`, `exo_recv`, `endpoint_send`, `endpoint_recv`
- Resource management: `set_gas`, `get_gas`, `set_numa_node`
- Capabilities: `cap_dec`, `cap_inc`
- Signal handling: `sigsend`
- Timer management: `set_timer_upcall`
- File control: `fcntl`

## Special Functions

### exo_pctr_transfer
A performance counter transfer function that handles architecture-specific register loading:
- **x86**: Loads value from stack into `%eax` register
- **x86_64**: Loads value from `%rdi` into `%rax` register
- Triggers `T_PCTR_TRANSFER` interrupt for performance counter data transfer between processes or kernel components

## Notes
- The `SYSCALL` macro automatically generates the appropriate assembly code for each architecture
- All system calls follow the standard calling convention for their respective architectures
- The `set_timer_upcall` system call is duplicated in the source and allows processes to handle timer interrupts in user space
#include "syscall.h"
#include "traps.h"

#ifndef __x86_64__
#define SYSCALL(name) \
  .globl name; \
  name: \
    movl $SYS_ ## name, %eax; \
    int $T_SYSCALL; \
    ret
#else
#define SYSCALL(name) \
  .globl name; \
  name: \
    movq $SYS_ ## name, %rax; \
    syscall; \
    ret
#endif

SYSCALL(fork)
SYSCALL(exit)
SYSCALL(wait)
SYSCALL(pipe)
SYSCALL(read)
SYSCALL(write)
SYSCALL(close)
SYSCALL(kill)
SYSCALL(exec)
SYSCALL(open)
SYSCALL(mknod)
SYSCALL(unlink)
SYSCALL(fstat)
SYSCALL(link)
SYSCALL(mkdir)
SYSCALL(chdir)
SYSCALL(dup)
SYSCALL(getpid)
SYSCALL(sbrk)
SYSCALL(sleep)
SYSCALL(uptime)
SYSCALL(mappte)


#ifndef __x86_64__
  .globl exo_pctr_transfer
exo_pctr_transfer:
  #ifndef __x86_64__
    # For non-x86_64 architectures:
    # Load the value from the stack into the eax register (4 bytes offset from esp).
    # The interrupt $T_PCTR_TRANSFER is used to transfer performance counter data
    # between processes or kernel components. It expects the data to be passed
    #ifndef __x86_64__
        movl 4(%esp), %eax
  #else
    #ifdef __x86_64__
      # For x86_64 architectures:
      # Load the value from the stack into the rax register (8 bytes offset from rsp).
      # The interrupt $T_PCTR_TRANSFER is used to transfer performance counter data
      # between processes or kernel components. It expects the data to be passed
      # in the rax register and triggers the transfer operation.
      movq 8(%rsp), %rax
    #endif
  #endif
    movq 8(%rsp), %rax
  #ifdef __x86_64__
    # For x86_64 architectures:
    # Move the value from rdi to rax and trigger the transfer operation.
  #else
    # For non-x86_64 architectures:
    # Load the value from the stack into eax.
    movl 4(%esp), %eax
  #endif
  movq %rdi, %rax
    movq %rdi, %rax
  #endif
  # The interrupt $T_PCTR_TRANSFER is used for transferring performance counter data
  # between processes or kernel space. It expects the relevant data to be passed
  # in the appropriate registers and handles the transfer accordingly.
  int $T_PCTR_TRANSFER
#endif

SYSCALL(set_timer_upcall)
// The set_timer_upcall system call sets a user-level upcall handler for timer events.
// This allows the process to handle timer interrupts in user space.
SYSCALL(set_timer_upcall)
SYSCALL(exo_unbind_page)
SYSCALL(exo_alloc_block)
SYSCALL(exo_bind_block)
SYSCALL(exo_flush_block)
SYSCALL(exo_yield_to)
SYSCALL(exo_read_disk)
SYSCALL(exo_write_disk)
SYSCALL(exo_send)
SYSCALL(exo_recv)
SYSCALL(endpoint_send)
SYSCALL(endpoint_recv)
SYSCALL(proc_alloc)
SYSCALL(set_gas)
SYSCALL(get_gas)
SYSCALL(set_numa_node)
SYSCALL(fcntl)
SYSCALL(sigsend)
SYSCALL(cap_dec)
SYSCALL(cap_inc)
SYSCALL(cap_dec)

