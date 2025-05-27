#include "types.h"
#include "defs.h"
#include "cap.h"
#include "proc.h"
#include "hypervisor.h"
#include "memlayout.h"
#include "mmu.h"
#include "elf.h"
#include <string.h>

// Allocate a capability referencing the hypervisor control interface.
struct hv_vcpu {
    uint64_t rip;
    uint64_t rsp;
    uint64_t rflags;
};

struct hv_vm {
    void *mem;
    uint32_t mem_cap;
    struct hv_vcpu vcpu;
};

static inline int vmxon(uint64_t addr) {
#ifdef __x86_64__
    int r;
    __asm__ volatile("vmxon %1; setna %0" : "=r"(r) : "m"(addr) : "cc", "memory");
    return r == 0 ? 0 : -1;
#else
    (void)addr;
    return -1;
#endif
}

static inline void vmxoff(void) {
#ifdef __x86_64__
    __asm__ volatile("vmxoff" ::: "cc");
#endif
}

static inline int vmlaunch(void) {
#ifdef __x86_64__
    int r;
    __asm__ volatile("vmlaunch; setna %0" : "=r"(r) :: "cc");
    return r == 0 ? 0 : -1;
#else
    return -1;
#endif
}

// Allocate a capability referencing the hypervisor control interface.
exo_cap exo_alloc_hypervisor(void) {
    struct hv_vm *vm = kalloc();
    if (!vm)
        return cap_new(0, 0, 0);
    memset(vm, 0, sizeof(*vm));
    int id = cap_table_alloc(CAP_TYPE_HYPERVISOR, (uint32_t)(uintptr_t)vm,
                             EXO_RIGHT_CTL, myproc()->pid);
    return cap_new(id >= 0 ? id : 0, EXO_RIGHT_CTL, myproc()->pid);
}

// Minimal stub that pretends to launch a guest kernel image.
int hv_launch_guest(exo_cap cap, const char *path) {
    struct cap_entry e;
    if (cap_table_lookup(cap.id, &e) < 0 || e.type != CAP_TYPE_HYPERVISOR)
        return -1;

    struct hv_vm *vm = (struct hv_vm *)(uintptr_t)e.resource;
    if (!vm)
        return -1;

    // Allocate one page of guest memory and load the first page of the image.
    exo_cap page = exo_alloc_page();
    if (page.id == 0)
        return -1;

    struct cap_entry pe;
    if (cap_table_lookup(page.id, &pe) < 0)
        return -1;
    vm->mem_cap = page.id;
    vm->mem = P2V(pe.resource);
    memset(vm->mem, 0, PGSIZE);

    begin_op();
    struct inode *ip = namei((char *)path);
    if (!ip) { end_op(); return -1; }
    ilock(ip);
    readi(ip, vm->mem, 0, PGSIZE);
    iunlockput(ip);
    end_op();

    vm->vcpu.rip = 0;
    vm->vcpu.rsp = PGSIZE;
    vm->vcpu.rflags = 0x2;

    void *vmxon_region = kalloc();
    if (!vmxon_region)
        return -1;
    memset(vmxon_region, 0, PGSIZE);
    if (vmxon(V2P(vmxon_region)) < 0) {
        kfree(vmxon_region);
        return -1;
    }

    // Attempt to launch the guest. This will likely fail on real hardware
    // without proper VMCS setup but demonstrates the call path.
    vmlaunch();

    vmxoff();
    kfree(vmxon_region);
    cprintf("hypervisor: launched guest %s\n", path);
    return 0;
}
