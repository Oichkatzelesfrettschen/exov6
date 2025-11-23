#include <types.h>
#include <exov6_interface.h>

extern int sys_create_env(void);
extern int sys_map_page(int target_env, uint64 phys, uint64 virt, int perm);
extern uint64 sys_alloc_page(void);

int
fork(void)
{
    int child_env_id = sys_create_env();
    if (child_env_id < 0) return -1;

    // Copy Heap (Simplified 1MB copy)
    // Note: Real implementation requires temporary mapping to copy data
    uint64 va;
    for (va = 0x40000000; va < 0x40010000; va += 4096) {
        uint64 pa_child = sys_alloc_page();
        if (pa_child == 0) continue;

        // TODO: Map pa_child into parent, copy data from va, unmap

        sys_map_page(child_env_id, pa_child, va, 0x7);
    }

    return child_env_id;
}
