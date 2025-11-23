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
