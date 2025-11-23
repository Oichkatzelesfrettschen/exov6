#include <types.h>
#include <defs.h>
#include <memlayout.h>
#include <mmu.h>
#include <param.h>
#include <proc.h>
#include <exov6_interface.h>

// User code makes a system call with INT T_SYSCALL.
// System call number in %eax.
// Arguments on the stack.

// Fetch the int at addr from the current process.
int fetchint(uintptr_t addr, int *ip) {
  struct proc *curproc = myproc();

  if (addr >= curproc->sz || addr + 4 > curproc->sz)
    return -1;
  *ip = *(int *)(addr);
  return 0;
}

// Fetch the nul-terminated string at addr from the current process.
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
  case 0: val = tf->rdi; break;
  case 1: val = tf->rsi; break;
  case 2: val = tf->rdx; break;
  case 3: val = tf->r10; break;
  case 4: val = tf->r8; break;
  case 5: val = tf->r9; break;
  default: return -1;
  }
  *ip = val;
  return 0;
#endif
}

// Fetch the nth 64-bit system call argument.
int arguint64(int n, uint64_t *ip) {
#ifndef __x86_64__
  // 32-bit implementation omitted for simplicity in this phase
  return -1;
#else
  uint64_t val;
  struct trapframe *tf = myproc()->tf;
  switch (n) {
  case 0: val = tf->rdi; break;
  case 1: val = tf->rsi; break;
  case 2: val = tf->rdx; break;
  case 3: val = tf->r10; break;
  case 4: val = tf->r8; break;
  case 5: val = tf->r9; break;
  default: return -1;
  }
  *ip = val;
  return 0;
#endif
}

// Fetch the nth word-sized system call argument as a pointer
int argptr(int n, char **pp, size_t size) {
  struct proc *curproc = myproc();
#ifndef __x86_64__
  int i;
  if (argint(n, &i) < 0)
    return -1;
  if (size < 0 || (uint32_t)i >= curproc->sz ||
      (uint32_t)i + size > curproc->sz)
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

// New Exokernel Syscalls
extern int sys_page_alloc(void);
extern int sys_page_map(void);
extern int sys_exit(void); // For SYS_env_destroy
extern int sys_uptime(void); // Keep for debug
extern int sys_cputs(void); // Bootstrap debug output

// Stubs for now (to be implemented)
int sys_env_create(void) { return -1; }
int sys_env_run(void) { return -1; }
int sys_page_unmap(void) { return -1; }
int sys_page_stat(void) { return -1; }
int sys_ipc_send(void) { return -1; }
int sys_ipc_recv(void) { return -1; }
int sys_set_label(void) { return -1; }
int sys_disk_io(void) { return -1; }

static int (*syscalls[])(void) = {
    [SYS_env_create] = sys_env_create,
    [SYS_env_run]    = sys_env_run,
    [SYS_env_destroy]= sys_exit,
    [SYS_page_alloc] = sys_page_alloc,
    [SYS_page_map]   = sys_page_map,
    [SYS_page_unmap] = sys_page_unmap,
    [SYS_page_stat]  = sys_page_stat,
    [SYS_ipc_send]   = sys_ipc_send,
    [SYS_ipc_recv]   = sys_ipc_recv,
    [SYS_set_label]  = sys_set_label,
    [SYS_disk_io]    = sys_disk_io,
    [SYS_cputs]      = sys_cputs,
};

void syscall(void) {
  int num;
  struct proc *curproc = myproc();

#ifndef __x86_64__
  num = curproc->tf->eax;
#else
  num = curproc->tf->rax;
#endif

  if (num > 0 && (size_t)num < NELEM(syscalls) && syscalls[num]) {
#ifndef __x86_64__
    curproc->tf->eax = syscalls[num]();
#else
    curproc->tf->rax = syscalls[num]();
#endif
  }
  else {
    cprintf("%d %s: unknown sys call %d\n", curproc->pid, curproc->name, num);
#ifndef __x86_64__
    curproc->tf->eax = -1;
#else
    curproc->tf->rax = -1;
#endif
  }
}
