// kernel/init_bin.S - Embed init binary into kernel
// This file includes the user init binary as raw data so the kernel
// can load it during userinit() without requiring a filesystem.

    .section .rodata

    // Page-align for efficient mapping
#if defined(__x86_64__) || defined(__i386__)
    .align 4096
#elif defined(__aarch64__)
    .p2align 12  // 4096 = 2^12
#else
    .align 4096
#endif

    .global _binary_init_start
    .global _binary_init_end
    .global _binary_init_size

_binary_init_start:
    .incbin "init.bin"
_binary_init_end:

#if defined(__x86_64__) || defined(__i386__)
    .align 4
#elif defined(__aarch64__)
    .p2align 2  // 4 = 2^2
#else
    .align 4
#endif

_binary_init_size:
    .long _binary_init_end - _binary_init_start
