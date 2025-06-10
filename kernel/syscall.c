
// clang-format off
#include "types.h"
#include "syscall.h"
#include "defs.h"
#include "memlayout.h"
#include "mmu.h"
#include "param.h"
#include "proc.h"
#include "x86.h"
// clang-format on


// User code makes a system call with INT T_SYSCALL.
// System call number in %eax.
// Arguments on the stack, from the user call to the C
// library system call function. The saved user %esp points
// to a saved program counter, and then the first argument.

// Fetch the int at addr from the current process.
int fetchint(uintptr_t addr, int *ip) {
  struct proc *curproc = myproc();

  if (addr >= curproc->sz || addr + 4 > curproc->sz)
    return -1;
  *ip = *(int *)(addr);
  return 0;
}

// Fetch the nul-terminated string at addr from the current process.
// Doesn't actually copy the string - just sets *pp to point at it.
// Returns length of string, not including nul.
int fetchstr(uintptr_t addr, char **pp) {
  char *s, *ep;
  struct proc *curproc = myproc();

  if (addr >= curproc->sz)
    return -1;
  *pp = (char *)addr;
  ep = (char *)curproc->sz;
  for (s = *pp; s < ep; s++) {
    if (*s == 0)
      return s - *pp;
  }
  return -1;
}

// Fetch the nth 32-bit system call argument.
int argint(int n, int *ip) {
#ifndef __x86_64__
  return fetchint((myproc()->tf->esp) + 4 + 4 * n, ip);
#else
  uint64_t val;
  struct trapframe *tf = myproc()->tf;
  switch (n) {
  case 0:
    val = tf->rdi;
    break;
  case 1:
    val = tf->rsi;
    break;
  case 2:
    val = tf->rdx;
    break;
  case 3:
    val = tf->r10;
    break;
  case 4:
    val = tf->r8;
    break;
  case 5:
    val = tf->r9;
    break;
  default:
    return -1;
  }
  *ip = val;
  return 0;
#endif
}

// Fetch the nth word-sized system call argument as a pointer
// to a block of memory of size bytes.  Check that the pointer
// lies within the process address space.
int
argptr(int n, char **pp, size_t size)
{
  struct proc *curproc = myproc();
#ifndef __x86_64__
  int i;
  if (argint(n, &i) < 0)
    return -1;
  if (size < 0 || (uint32_t)i >= curproc->sz || (uint32_t)i + size > curproc->sz)
    return -1;
  *pp = (char *)i;
  return 0;
#else
  uint64_t addr;
  if (argint(n, (int *)&addr) < 0)
    return -1;
  if (size < 0 || addr >= curproc->sz || addr + size > curproc->sz)
    return -1;
  *pp = (char *)addr;
  return 0;
#endif
}

// Fetch the nth word-sized system call argument as a string pointer.
// Check that the pointer is valid and the string is nul-terminated.
// (There is no shared writable memory, so the string can't change
// between this check and being used by the kernel.)
int argstr(int n, char **pp) {
#ifndef __x86_64__
  int addr;
  if (argint(n, &addr) < 0)
    return -1;
  return fetchstr(addr, pp);
#else
  uint64_t addr;
  if (argint(n, (int *)&addr) < 0)
    return -1;
  return fetchstr(addr, pp);
#endif
}

extern int sys_chdir(void);
extern int sys_close(void);
extern int sys_dup(void);
extern int sys_exec(void);
extern int sys_exit(void);
extern int sys_fork(void);
extern int sys_getpid(void);
extern int sys_kill(void);
extern int sys_pipe(void);
extern int sys_sbrk(void);
extern int sys_sleep(void);
extern int sys_wait(void);
extern int sys_uptime(void);
extern int sys_mappte(void);
extern int sys_set_timer_upcall(void);
extern int sys_exo_alloc_page(void);
extern int sys_exo_unbind_page(void);
extern int sys_exo_alloc_block(void);
extern int sys_exo_bind_block(void);
extern int sys_exo_yield_to(void);
extern int sys_exo_read_disk(void);
extern int sys_exo_write_disk(void);
extern int sys_exo_send(void);
extern int sys_exo_recv(void);
extern int sys_exo_recv_timed(void);
extern int sys_exo_alloc_ioport(void);
extern int sys_exo_bind_irq(void);
extern int sys_exo_alloc_dma(void);
extern int sys_endpoint_send(void);
extern int sys_endpoint_recv(void);
extern int sys_proc_alloc(void);
extern int sys_set_gas(void);
extern int sys_get_gas(void);
extern int sys_set_numa_node(void);
extern int sys_ipc_fast(void);
extern int sys_fcntl(void);
extern int sys_sigsend(void);
extern int sys_sigcheck(void);
extern int sys_cap_inc(void);
extern int sys_cap_dec(void);

static int (*syscalls[])(void) = {
    [SYS_fork] sys_fork,
    [SYS_exit] sys_exit,
    [SYS_wait] sys_wait,
    [SYS_pipe] sys_pipe,
    [SYS_kill] sys_kill,
    [SYS_exec] sys_exec,
    [SYS_getpid] sys_getpid,
    [SYS_sbrk] sys_sbrk,
    [SYS_sleep] sys_sleep,
    [SYS_uptime] sys_uptime,
    [SYS_mappte] sys_mappte,
    [SYS_set_timer_upcall] sys_set_timer_upcall,
    [SYS_exo_alloc_page] sys_exo_alloc_page,
    [SYS_exo_unbind_page] sys_exo_unbind_page,
    [SYS_exo_alloc_block] sys_exo_alloc_block,
    [SYS_exo_bind_block] sys_exo_bind_block,
    [SYS_exo_yield_to] sys_exo_yield_to,
    [SYS_exo_read_disk] sys_exo_read_disk,
    [SYS_exo_write_disk] sys_exo_write_disk,
    [SYS_exo_alloc_ioport] sys_exo_alloc_ioport,
    [SYS_exo_bind_irq] sys_exo_bind_irq,
    [SYS_exo_alloc_dma] sys_exo_alloc_dma,
    [SYS_exo_send] sys_exo_send,
    [SYS_exo_recv] sys_exo_recv,
    [SYS_exo_recv_timed] sys_exo_recv_timed,
    [SYS_endpoint_send] sys_endpoint_send,
    [SYS_endpoint_recv] sys_endpoint_recv,
    [SYS_proc_alloc] sys_proc_alloc,
    [SYS_set_gas] sys_set_gas,
    [SYS_get_gas] sys_get_gas,
    [SYS_set_numa_node] sys_set_numa_node,
    [SYS_fcntl] sys_fcntl,
    [SYS_sigsend] sys_sigsend,
    [SYS_sigcheck] sys_sigcheck,
    [SYS_cap_inc] sys_cap_inc,
    [SYS_cap_dec] sys_cap_dec,
    [SYS_ipc_fast] sys_ipc_fast,
};

void syscall(void) {
  int num;
  struct proc *curproc = myproc();
#ifndef __x86_64__
  num = curproc->tf->eax;
#else
  num = curproc->tf->rax;
#endif
  if(num == 0x30){
#ifdef __x86_64__
    curproc->tf->rax = sys_ipc_fast();
#else
    curproc->tf->eax = sys_ipc_fast();
#endif
    return;
  }
  if (num > 0 && num < NELEM(syscalls) && syscalls[num]) {
#ifndef __x86_64__
    curproc->tf->eax = syscalls[num]();
#else
    curproc->tf->rax = syscalls[num]();
#endif
  } else {
    cprintf("%d %s: unknown sys call %d\n", curproc->pid, curproc->name, num);
#ifndef __x86_64__
    curproc->tf->eax = -1;
#else
    curproc->tf->rax = -1;
#endif
  }
}
