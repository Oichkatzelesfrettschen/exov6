# Porting and Multi-Architecture Guide

This guide explains the multi-architecture support in FeuerBird and how to port the kernel to a new architecture.

## Supported Architectures

FeuerBird supports several CPU architectures through a combination of cross compilers and runtime feature detection.

* `x86` (32‑bit)
* `x86_64` (Tier-1 Reference)
* `aarch64` (Tier-2)
* `arm` (ARMv7)
* `powerpc`
* `ppc64` (big‑endian PowerPC64)
* `ppc64le` (little‑endian PowerPC64)

The build system selects the target via `-DARCH=<arch>`.

## Porting to a New Architecture

To port FeuerBird to a new architecture (e.g., RISC-V), follow these steps:

### 1. Build System Integration

1.  **Add Toolchain**: Update `cmake/toolchains/` with a new toolchain file (e.g., `riscv64.cmake`).
2.  **Update CMakeLists.txt**: Add the new architecture to the allowed `ARCH` list and configure specific compiler flags.

### 2. HAL Implementation (`include/hal/`)

Implement the Hardware Abstraction Layer defined in `include/hal/arch_ops.h`:

*   **Interrupts**: `hal_irq_enable()`, `hal_irq_disable()`
*   **Context Switching**: `hal_switch_context()`
*   **Memory Barriers**: `hal_barrier()`
*   **Time**: `hal_get_time()`

### 3. Kernel Architecture Code (`kernel/arch/<new_arch>/`)

*   **Boot Code**: `start.S` or `head.S` (Assembly entry point).
*   **Trap Handling**: Interrupt vector table and trap dispatcher.
*   **Memory Management**: Page table manipulation specific to the MMU (e.g., Sv39/Sv48 for RISC-V).

### 4. LibOS ABI (`libos/arch/riscv64/`)

*   **Syscall Entry**: Implement `syscall_entry.S`.
*   **Signal Handling**: Stack frame setup for signal delivery.
*   **Thread Local Storage**: TLS register initialization.

### 5. Runtime Feature Detection

If the architecture supports SIMD or other extensions, implement runtime detection in `arch/simd_dispatch.c`.

## Runtime Feature Detection (SIMD)

When `USE_SIMD` is enabled, the runtime checks the host CPU before dispatching vectorised routines.

### Supported Backends

* x86: AVX-512, AVX2, AVX, SSE3, SSE2, MMX
* ARM: NEON
* PowerPC: AltiVec/VSX

### POSIX Wrappers

User programs link against `libos.a`. Math helpers in `user/math_core.c` forward to the dispatch library to use the best available SIMD backend automatically.

## Build Variants

The script `scripts/build_isa_variants.sh` demonstrates building kernels for different instruction set variants.
