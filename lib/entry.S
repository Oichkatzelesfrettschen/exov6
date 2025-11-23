// lib/entry.S - LibOS entry point
// Architecture-conditional assembly

.global _start

#if defined(__x86_64__)
// ═══════════════════════════════════════════════════════════════════
// x86_64 Entry Point
// ═══════════════════════════════════════════════════════════════════
_start:
    // Kernel sets up stack pointer (RSP)

    // Call LibOS runtime entry point
    call libmain

    // Exit (SYS_env_destroy = 3)
    mov $3, %rax
    syscall

    // Should not reach here
    ud2

#elif defined(__aarch64__)
// ═══════════════════════════════════════════════════════════════════
// ARM64 Entry Point
// ═══════════════════════════════════════════════════════════════════
_start:
    // Kernel sets up stack pointer (SP)

    // Call LibOS runtime entry point
    // On macOS, C symbols have underscore prefix
#ifdef __APPLE__
    bl _libmain
#else
    bl libmain
#endif

    // Exit (SYS_env_destroy = 3)
    mov x8, #3
    svc #0

    // Should not reach here
    brk #0

#else
#error "Unsupported architecture for lib/entry.S"
#endif
