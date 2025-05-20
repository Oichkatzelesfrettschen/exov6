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
  movl 4(%esp), %eax
  int $T_PCTR_TRANSFER
  ret
#else
  .globl exo_pctr_transfer
exo_pctr_transfer:
  movq %rdi, %rax
  int $T_PCTR_TRANSFER
  ret
#endif

SYSCALL(set_timer_upcall)
SYSCALL(exo_alloc_page)
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
SYSCALL(set_numa_node)


