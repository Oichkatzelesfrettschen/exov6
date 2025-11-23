#include <types.h>
#include <exov6_interface.h>

// Architecture-conditional syscall wrapper
static uint64
syscall(int num, uint64 a0, uint64 a1, uint64 a2, uint64 a3)
{
    uint64 ret;

#if defined(__x86_64__)
    // x86_64: syscall instruction with register ABI
    register uint64 r10 asm("r10") = a3;
    asm volatile("syscall"
                 : "=a" (ret)
                 : "a" (num), "D" (a0), "S" (a1), "d" (a2), "r" (r10)
                 : "rcx", "r11", "memory");

#elif defined(__aarch64__)
    // ARM64: svc #0 instruction
    // Syscall number in x8, arguments in x0-x5, return in x0
    register uint64 x8 __asm__("x8") = (uint64)num;
    register uint64 x0 __asm__("x0") = a0;
    register uint64 x1 __asm__("x1") = a1;
    register uint64 x2 __asm__("x2") = a2;
    register uint64 x3 __asm__("x3") = a3;
    __asm__ volatile("svc #0"
                     : "=r" (x0)
                     : "r" (x8), "r" (x0), "r" (x1), "r" (x2), "r" (x3)
                     : "memory");
    ret = x0;

#else
    #error "Unsupported architecture for syscall wrapper"
#endif

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

// --- Bootstrap Debug ---

void sys_cputs(const char *s, int len) {
    syscall(SYS_cputs, (uint64)s, (uint64)len, 0, 0);
}

// --- Exception/Upcall Handling ---

// Register an exception handler and exception stack
// handler_va: Address of upcall entry point
// stack_va: Top of exception stack (grows down)
int sys_env_set_handler(uint64 handler_va, uint64 stack_va) {
    return (int)syscall(SYS_env_set_handler, handler_va, stack_va, 0, 0);
}

// Return from upcall, restoring saved context
// tf: Pointer to ExoTrapFrame on exception stack
int sys_env_resume(struct ExoTrapFrame *tf) {
    return (int)syscall(SYS_env_resume, (uint64)tf, 0, 0, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// IPC (Phase 9 - Inter-Process Communication)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Send a message to another process
 * @param target_pid Destination process ID
 * @param w0, w1, w2 Message data words
 * @return 0 on success, negative on error
 */
int sys_ipc_send(int target_pid, uint64 w0, uint64 w1, uint64 w2) {
    return (int)syscall(SYS_ipc_send, (uint64)target_pid, w0, w1, w2);
}

/**
 * Receive a message (blocking)
 * @param sender_pid Pointer to store sender's PID
 * @param w0, w1, w2 Pointers to store message data
 * @return 0 on success, negative on error
 */
int sys_ipc_recv(int *sender_pid, uint64 *w0, uint64 *w1, uint64 *w2) {
    return (int)syscall(SYS_ipc_recv, (uint64)sender_pid, (uint64)w0,
                        (uint64)w1, (uint64)w2);
}
