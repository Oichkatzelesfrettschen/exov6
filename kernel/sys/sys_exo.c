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
