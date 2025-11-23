#include <types.h>
#include <exov6_interface.h>

extern uint64 sys_alloc_page(void);
extern int sys_map_page(int target_env, uint64 phys, uint64 virt, int perm);

#define HEAP_START 0x40000000
static uint64 heap_ptr = HEAP_START;

void*
malloc(uint64 size)
{
    if (size == 0) return 0;

    uint64 phys_addr = sys_alloc_page();
    if (phys_addr == 0) return 0; // OOM

    // Map into SELF (0) at heap_ptr
    // Permission 0x7 = R|W|X (if 0x1=R, 0x2=W, 0x4=X or U?)
    // mmu.h: PERM_R=1, PERM_W=2, PERM_X=4. So 0x7 is RWX.
    if (sys_map_page(0, phys_addr, heap_ptr, 0x7) < 0) {
        return 0;
    }

    void* ptr = (void*)heap_ptr;
    heap_ptr += 4096; // Simple bump allocator (one page per alloc)
    return ptr;
}

void free(void* ptr) {
    // No-op
    (void)ptr;
}
