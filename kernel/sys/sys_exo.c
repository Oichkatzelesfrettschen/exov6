#include <types.h>
#include <defs.h>
#include <param.h>
#include <memlayout.h>
#include <spinlock.h>
#include <proc.h>
#include <exov6_interface.h>
#include "../mem/mm.h"
#include <mmu.h>

// SYS_page_alloc: LibOS asks for a physical page
// Returns: Physical Address (Handle)
uint64
sys_page_alloc(void)
{
    void *mem = kalloc();
    if(mem == 0) return -1;

    // Set Owner
    // PA2PAGE expects Kernel Virtual Address (handle)
    struct PageInfo *pp = PA2PAGE(mem);
    pp->owner_env = myproc()->pid;
    pp->label = myproc()->label; // Inherit label from creator
    page_incref((uint64)mem);

    return (uint64)mem;
}

// SYS_page_map: LibOS maps a physical page to virtual address
// Prototype: sys_page_map(int target_env, uint64 phys_addr, uint64 virt_addr, int perm)
uint64
sys_page_map(void)
{
    uint64 phys_addr, virt_addr;
    int target_env_id, perm;

    // Arg 0: target_env (int)
    if (argint(0, &target_env_id) < 0) return -1;

    // Arg 1: phys_addr (uint64)
    if (arguint64(1, &phys_addr) < 0) return -1;

    // Arg 2: virt_addr (uint64)
    if (arguint64(2, &virt_addr) < 0) return -1;

    // Arg 3: perm (int)
    if (argint(3, &perm) < 0) return -1;

    struct proc *target;
    if (target_env_id == 0 || target_env_id == myproc()->pid) {
        target = myproc();
    } else {
        target = find_proc(target_env_id);
        if (!target) return -1;
    }

    // Check if this is an MMIO mapping (device memory, not RAM)
    // MMIO addresses are below KERNBASE or above PHYSTOP
    int is_mmio = (phys_addr < KERNBASE && phys_addr >= 0x10000000ULL) ||
                  (phys_addr >= PHYSTOP);

    if (is_mmio) {
        // MMIO mapping - requires HIGH label (privileged process)
        if (target->label != LABEL_HIGH) {
            cprintf("MMIO denied: Process %d lacks LABEL_HIGH\n", target->pid);
            return -1;
        }
        // For MMIO, we map the physical address directly (no V2P conversion)
        // Sanitize permissions
        perm &= (PERM_R | PERM_W | PERM_X);

        if(insert_pte(target->pgdir, (void*)virt_addr, phys_addr, perm) < 0)
            return -1;

        return 0;  // No reference tracking for device memory
    }

    // Regular RAM mapping
    // PA2PAGE expects Kernel Virtual Address (handle)
    struct PageInfo *pp = PA2PAGE(phys_addr);

    // 1. LATTICE CHECK
    if (!can_flow(pp->label, target->label)) {
        cprintf("Security Violation: Label %d -> Label %d\n", pp->label, target->label);
        return -1;
    }

    // 2. SANITIZE PERMISSIONS
    // Force user bit for all user mappings. Strip dangerous bits.
    // Allow only R, W, X from user; insert_pte will add PTE_U.
    perm &= (PERM_R | PERM_W | PERM_X);

    // 3. Map it
    // insert_pte expects Physical Address (hardware), not Kernel Virtual Address (handle)
    if(insert_pte(target->pgdir, (void*)virt_addr, V2P(phys_addr), perm) < 0)
        return -1;

    // 4. Track Reference
    page_incref(phys_addr);

    return 0;
}

// SYS_cputs: Debug syscall - print string to console
// This gives the LibOS "eyes" during bootstrap
// Args: (const char *buf, int len)
uint64
sys_cputs(void)
{
    uint64 buf_addr;
    int len;

    // 1. Fetch arguments (buffer pointer, length)
    if(arguint64(0, &buf_addr) < 0 || argint(1, &len) < 0)
        return -1;

    // 2. Bounds check
    if(len < 0 || len > 4096)  // Max 4KB per call
        return -1;

    struct proc *p = myproc();

    // 3. Loop and print (using uva2ka for safe access)
    for(int i = 0; i < len; i++){
        // Translate user virtual address to kernel address
        char *ka = uva2ka(p->pgdir, (char*)(buf_addr + i));
        if(ka == 0)
            break;  // Invalid address
        uartputc(*ka);
    }

    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// SYS_env_set_handler: Register upcall handler for exceptions
// ═══════════════════════════════════════════════════════════════════════════
// Args: (uint64 handler_va, uint64 exception_stack_va)
// The LibOS says: "If I crash or get interrupted, jump to handler_va
// using exception_stack_va as the stack."
uint64
sys_env_set_handler(void)
{
    uint64 handler_va, stack_va;

    if(arguint64(0, &handler_va) < 0 || arguint64(1, &stack_va) < 0)
        return -1;

    // Basic validation: handler must be in user space
    if(handler_va >= KERNBASE || stack_va >= KERNBASE)
        return -1;

    struct proc *p = myproc();
    p->upcall_handler = handler_va;
    p->upcall_stack = stack_va;
    p->in_upcall = 0;  // Reset upcall state

    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// SYS_env_resume: Return from upcall, restore saved context
// ═══════════════════════════════════════════════════════════════════════════
// Args: (struct ExoTrapFrame *tf)
// The LibOS exception handler calls this to restore the original context
// and resume execution at the faulting instruction (or skip it).
uint64
sys_env_resume(void)
{
    uint64 tf_addr;

    if(arguint64(0, &tf_addr) < 0)
        return -1;

    struct proc *p = myproc();

    // Copy the ExoTrapFrame from user space
    struct ExoTrapFrame utf;
    if(copyin(p->pgdir, (char*)&utf, tf_addr, sizeof(utf)) < 0)
        return -1;

    // Restore the trapframe from the ExoTrapFrame
    // Architecture-specific: x86_64
#ifdef __x86_64__
    p->tf->rip = utf.rip;
    p->tf->rflags = utf.rflags;
    p->tf->rsp = utf.rsp;
    p->tf->rax = utf.rax;
    p->tf->rbx = utf.rbx;
    p->tf->rcx = utf.rcx;
    p->tf->rdx = utf.rdx;
    p->tf->rsi = utf.rsi;
    p->tf->rdi = utf.rdi;
    p->tf->rbp = utf.rbp;
    p->tf->r8 = utf.r8;
    p->tf->r9 = utf.r9;
    p->tf->r10 = utf.r10;
    p->tf->r11 = utf.r11;
    p->tf->r12 = utf.r12;
    p->tf->r13 = utf.r13;
    p->tf->r14 = utf.r14;
    p->tf->r15 = utf.r15;
#else
    // 32-bit x86 fallback
    p->tf->eip = (uint32)utf.rip;
    p->tf->eflags = (uint32)utf.rflags;
    p->tf->esp = (uint32)utf.rsp;
    p->tf->eax = (uint32)utf.rax;
    p->tf->ebx = (uint32)utf.rbx;
    p->tf->ecx = (uint32)utf.rcx;
    p->tf->edx = (uint32)utf.rdx;
    p->tf->esi = (uint32)utf.rsi;
    p->tf->edi = (uint32)utf.rdi;
    p->tf->ebp = (uint32)utf.rbp;
#endif

    // Clear upcall flag
    p->in_upcall = 0;

    // Return will go through usertrapret, which will restore the context
    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// SYS_env_create: Create a new blank environment (Phase 10)
// ═══════════════════════════════════════════════════════════════════════════
//
// EXOKERNEL PHILOSOPHY:
//   The kernel creates a BLANK process with:
//     - Kernel stack (for syscalls/traps)
//     - Empty page table (kernel mappings only)
//     - Initial security label (inherited from parent)
//
//   The LIBOS is responsible for:
//     - Allocating user memory (sys_page_alloc)
//     - Mapping ELF segments (sys_page_map)
//     - Setting entry point (sys_env_run)
//
// This is inspired by:
//   - MIT Exokernel: env_create() in xok/sys/env.c
//   - seL4: seL4_Untyped_Retype for TCB creation
//
// Returns: New environment's PID on success, -1 on failure
uint64
sys_env_create(void)
{
    struct proc *parent = myproc();
    struct proc *child;

    // 1. Allocate process structure (kernel stack, trapframe, context)
    child = allocproc();
    if(child == 0)
        return -1;

    // 2. Create empty page table with kernel mappings
    child->pgdir = setupkvm();
    if(child->pgdir == 0){
        // Clean up on failure
        kfree(child->kstack);
        child->kstack = 0;
        if(child->mailbox){
            kfree((char*)child->mailbox);
            child->mailbox = 0;
        }
        child->state = UNUSED;
        return -1;
    }

    // 3. Inherit security label from parent
    child->label = parent->label;

    // 4. Set parent relationship
    child->parent = parent;

    // 5. Initialize user-space fields to blank state
    child->sz = 0;              // No user memory yet
    child->upcall_handler = 0;  // No exception handler
    child->upcall_stack = 0;
    child->in_upcall = 0;

    // 6. Initialize trapframe to safe defaults
    memset(child->tf, 0, sizeof(*child->tf));
#ifdef __x86_64__
    child->tf->cs = (SEG_UCODE << 3) | DPL_USER;
    child->tf->ss = (SEG_UDATA << 3) | DPL_USER;
    child->tf->rflags = FL_IF;  // Enable interrupts in user mode
    // rip and rsp will be set by sys_env_run()
#else
    child->tf->cs = (SEG_UCODE << 3) | DPL_USER;
    child->tf->ds = (SEG_UDATA << 3) | DPL_USER;
    child->tf->es = child->tf->ds;
    child->tf->ss = child->tf->ds;
    child->tf->eflags = FL_IF;
#endif

    // 7. Give initial gas budget (can be adjusted later)
    child->gas_remaining = 0x10000;  // Reasonable default
    child->out_of_gas = 0;

    // 8. Copy name from parent (can be changed later)
    safestrcpy(child->name, "child", sizeof(child->name));

    // 9. Inherit current working directory
    if(parent->cwd)
        child->cwd = idup(parent->cwd);

    // Child stays in EMBRYO state until sys_env_run() is called
    // This allows LibOS to set up memory before starting execution

    cprintf("[EXOKERNEL] env_create: PID %d created by PID %d\n",
            child->pid, parent->pid);

    return child->pid;
}

// ═══════════════════════════════════════════════════════════════════════════
// SYS_env_run: Start/resume execution of an environment (Phase 10)
// ═══════════════════════════════════════════════════════════════════════════
//
// EXOKERNEL PHILOSOPHY:
//   This is a "scheduler activation" - the LibOS explicitly yields to
//   a specific environment rather than relying on kernel scheduling.
//
//   The kernel only validates that:
//     - Target environment exists and is owned by caller (or is self)
//     - Target has valid entry point and stack
//
// Args: (int env_id, uint64 entry_point, uint64 stack_pointer)
//   env_id = 0 means "run myself with new entry point" (exec-like)
//   env_id > 0 means "start this child environment"
//
// Inspired by:
//   - MIT Exokernel: yield() with explicit target
//   - seL4: seL4_TCB_Resume
//   - L4: ThreadSwitch
//
// Returns: Does not return on success (switches to target)
//          Returns -1 on error
uint64
sys_env_run(void)
{
    int env_id;
    uint64 entry_point, stack_ptr;

    if(argint(0, &env_id) < 0)
        return -1;
    if(arguint64(1, &entry_point) < 0)
        return -1;
    if(arguint64(2, &stack_ptr) < 0)
        return -1;

    struct proc *caller = myproc();
    struct proc *target;

    // Find target environment
    if(env_id == 0 || env_id == caller->pid){
        // Self-exec: replace current context
        target = caller;
    } else {
        // Start child: must be our child in EMBRYO state
        target = find_proc(env_id);
        if(target == 0){
            cprintf("[EXOKERNEL] env_run: PID %d not found\n", env_id);
            return -1;
        }

        // Security check: must be our child
        if(target->parent != caller){
            cprintf("[EXOKERNEL] env_run: PID %d not child of PID %d\n",
                    env_id, caller->pid);
            return -1;
        }

        // Must be in EMBRYO state (not yet running)
        if(target->state != EMBRYO){
            cprintf("[EXOKERNEL] env_run: PID %d not in EMBRYO state\n", env_id);
            return -1;
        }
    }

    // Validate addresses (must be in user space)
    if(entry_point >= KERNBASE || stack_ptr >= KERNBASE){
        cprintf("[EXOKERNEL] env_run: invalid addresses\n");
        return -1;
    }

    // Set up target's execution context
#ifdef __x86_64__
    target->tf->rip = entry_point;
    target->tf->rsp = stack_ptr;
#else
    target->tf->eip = (uint32)entry_point;
    target->tf->esp = (uint32)stack_ptr;
#endif

    cprintf("[EXOKERNEL] env_run: Starting PID %d at 0x%lx, sp=0x%lx\n",
            target->pid, entry_point, stack_ptr);

    // If starting a child, make it runnable
    if(target != caller){
        extern struct ptable ptable;
        acquire_compat(&ptable.lock);
        target->state = RUNNABLE;
        release_compat(&ptable.lock);
        // Return to caller - child will be scheduled later
        return 0;
    }

    // Self-exec case: this never returns
    // The trapframe has been updated, so when we return to user space
    // we'll jump to the new entry point
    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// SYS_cgetc: Get character from console (Phase 11b - "The Sense")
// ═══════════════════════════════════════════════════════════════════════════
//
// LIONS' LESSON: In a pure exokernel, we'd export the keyboard hardware
// directly to user space. For simplicity, we use the kernel's tty buffer.
//
// This blocks until a character is available.
// In the future, this could be replaced by:
//   1. MMIO-mapped keyboard port (PS/2)
//   2. USB keyboard driver in user space
//   3. IPC to a console server
//
// Returns: Character read (0-255), or -1 on error

// External tty structure (from kernel/tty.c)
extern struct {
    struct spinlock lock;
    char buf[128];
    uint32_t r;  // read index
    uint32_t w;  // write index
    uint32_t e;  // edit index
} tty;

uint64
sys_cgetc(void)
{
    struct proc *p = myproc();
    int c;

    acquire(&tty.lock);

    // Block until input is available
    while(tty.r == tty.w) {
        // Check if we've been killed
        if(p->killed) {
            release(&tty.lock);
            return -1;
        }
        // Sleep on tty.r channel (woken by ttyintr when input arrives)
        sleep(&tty.r, &tty.lock);
    }

    // Read one character
    c = tty.buf[tty.r++ % 128];

    release(&tty.lock);

    return (uint64)(unsigned char)c;
}

// ═══════════════════════════════════════════════════════════════════════════
// SYS_env_wait: Wait for child environment to exit (Phase 11b - "The Patience")
// ═══════════════════════════════════════════════════════════════════════════
//
// LIONS' LESSON: In UNIX V6, wait() is complex because of process groups.
// Here we have a simpler model: wait for a specific child to exit.
//
// Args: (int child_pid)
// Returns: Exit status of child, or -1 on error
//
// The caller blocks until the specified child exits (becomes ZOMBIE).
// The zombie is then reaped (freed).

uint64
sys_env_wait(void)
{
    int child_pid;
    struct proc *p = myproc();
    struct proc *child;
    int exit_status;

    if(argint(0, &child_pid) < 0)
        return -1;

    // Find the child process
    extern struct ptable ptable;
    acquire_compat(&ptable.lock);

    child = 0;
    for(struct proc *pp = ptable.proc; pp < &ptable.proc[NPROC]; pp++) {
        if(pp->pid == child_pid && pp->parent == p) {
            child = pp;
            break;
        }
    }

    if(child == 0) {
        release_compat(&ptable.lock);
        return -1;  // Not our child or doesn't exist
    }

    // Wait for child to become ZOMBIE
    while(child->state != ZOMBIE) {
        if(p->killed) {
            release_compat(&ptable.lock);
            return -1;
        }
        // Sleep on parent (exit() wakes parent via wakeup(curproc->parent))
        sleep(p, &ptable.lock);
    }

    // Reap the zombie
    exit_status = child->exit_status;

    // Free child's kernel stack and process slot
    kfree(child->kstack);
    child->kstack = 0;
    if(child->pgdir)
        freevm(child->pgdir);
    child->pgdir = 0;
    child->pid = 0;
    child->parent = 0;
    child->name[0] = 0;
    child->killed = 0;
    child->state = UNUSED;

    release_compat(&ptable.lock);

    cprintf("[EXOKERNEL] env_wait: Child PID %d exited with status %d\n",
            child_pid, exit_status);

    return exit_status;
}
