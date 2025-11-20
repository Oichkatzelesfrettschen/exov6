#include <types.h>
#include "param.h"
#include "mmu.h"
#include <arch.h>
#include "spinlock.h"

// Minimal syscall implementation for Phase 2
// Replaces the stub syscalls in kernel/exo.c

// External functions we'll need
extern void kprintf(const char *fmt, ...);
extern void panic(const char *s);
extern struct proc* allocproc(void);

// Process states
#define UNUSED  0
#define EMBRYO  1
#define RUNNABLE 2
#define RUNNING 3
#define ZOMBIE  4

// Simple process structure (should match main_minimal.c)
struct proc {
    int pid;
    int state;
    char name[16];
};

extern struct proc proc_table[64];
extern int next_pid;

// Global current process pointer
struct proc *curproc = 0;

// System call numbers
#define SYS_exit   1
#define SYS_fork   2
#define SYS_read   3
#define SYS_write  4
#define SYS_exec   7

// Syscall implementations

int sys_exit(void) {
    if (!curproc) return -1;
    
    kprintf("Process %d exiting\n", curproc->pid);
    curproc->state = ZOMBIE;
    
    // In real kernel, would clean up process resources
    // and wake up parent process
    
    // Never return from exit
    for(;;) {
#ifdef __x86_64__
        __asm__ volatile("hlt");
#elif defined(__aarch64__)
        __asm__ volatile("wfi");
#else
        while(1);
#endif
    }
}

int sys_fork(void) {
    struct proc *np = allocproc();
    if (!np) {
        kprintf("fork: no free process\n");
        return -1;
    }
    
    // Copy parent process
    if (curproc) {
        // Copy process name
        for (int i = 0; i < 16; i++) {
            np->name[i] = curproc->name[i];
        }
        kprintf("forked process %d from %d\n", np->pid, curproc->pid);
    } else {
        // No parent - this is init
        for (int i = 0; i < 16; i++) {
            np->name[i] = "child"[i];
            if (np->name[i] == 0) break;
        }
        np->name[15] = 0;
        kprintf("forked process %d (init)\n", np->pid);
    }
    
    np->state = RUNNABLE;
    
    // Return child PID to parent, 0 to child
    // For now, just return child PID
    return np->pid;
}

int sys_read(void) {
    // Arguments: fd, buf, count
    // For now, minimal implementation
    kprintf("read syscall called\n");
    return 0;  // Read 0 bytes
}

int sys_write(void) {
    // Arguments: fd, buf, count  
    // For now, minimal implementation that just prints
    kprintf("write syscall called\n");
    return 1;  // Wrote 1 byte
}

int sys_exec(void) {
    // Arguments: path, argv
    kprintf("exec syscall called\n");
    
    if (!curproc) return -1;
    
    // For now, just change the process name to indicate exec
    for (int i = 0; i < 16; i++) {
        curproc->name[i] = "exec"[i];
        if (curproc->name[i] == 0) break;
    }
    curproc->name[15] = 0;
    
    kprintf("exec completed for process %d\n", curproc->pid);
    return 0;
}

// Syscall dispatch table
static int (*syscalls[])(void) = {
[SYS_exit]  = sys_exit,
[SYS_fork]  = sys_fork,
[SYS_read]  = sys_read,
[SYS_write] = sys_write,
[SYS_exec]  = sys_exec,
};

// Main syscall handler
void syscall(void) {
    int num;
    
    if (!curproc) {
        panic("syscall: no current process");
    }
    
    // Get syscall number (normally from registers/trapframe)
    // For now, simulate with a test sequence
    static int test_syscall = SYS_write;
    num = test_syscall;
    
    kprintf("syscall %d from process %d\n", num, curproc->pid);
    
    if (num > 0 && (size_t)num < sizeof(syscalls)/sizeof(syscalls[0]) && syscalls[num]) {
        // Call the syscall function
        int result = syscalls[num]();
        kprintf("syscall %d returned %d\n", num, result);
        
        // Store result (normally in registers/trapframe)
        // For now, just print it
        
    } else {
        kprintf("bad syscall %d from process %d\n", num, curproc->pid);
        // Kill the process
        curproc->state = ZOMBIE;
    }
}

// Initialize syscall system
void syscall_init(void) {
    kprintf("Syscall system initialized\n");
    kprintf("Available syscalls: exit(%d), fork(%d), read(%d), write(%d), exec(%d)\n",
            SYS_exit, SYS_fork, SYS_read, SYS_write, SYS_exec);
}
