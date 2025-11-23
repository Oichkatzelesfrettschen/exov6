.global _start
_start:
    # Kernel sets up stack pointer (RSP)

    # Call LibOS runtime entry point
    call libmain

    # Exit
    mov $3, %rax # SYS_env_destroy
    syscall
