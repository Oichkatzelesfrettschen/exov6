#include <types.h>
#include <exov6_interface.h>

// x86_64 Syscall Wrapper
static uint64
syscall(int num, uint64 a0, uint64 a1, uint64 a2, uint64 a3)
{
    uint64 ret;
    register uint64 r10 asm("r10") = a3;
    asm volatile("syscall"
                 : "=a" (ret)
                 : "a" (num), "D" (a0), "S" (a1), "d" (a2), "r" (r10)
                 : "rcx", "r11", "memory");
    return ret;
}

// --- The Primitives ---

uint64 sys_alloc_page(void) {
    return syscall(SYS_page_alloc, 0, 0, 0, 0);
}

int sys_map_page(int target_env, uint64 phys, uint64 virt, int perm) {
    return (int)syscall(SYS_page_map, (uint64)target_env, phys, virt, (uint64)perm);
}

int sys_create_env(void) {
    return (int)syscall(SYS_env_create, 0, 0, 0, 0);
}

int sys_run_env(int envid) {
    return (int)syscall(SYS_env_run, (uint64)envid, 0, 0, 0);
}

void sys_yield(void) {
    syscall(SYS_env_run, 0, 0, 0, 0);
}
