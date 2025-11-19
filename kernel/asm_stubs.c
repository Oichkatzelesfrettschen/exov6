/**
 * @file asm_stubs.c
 * @brief Assembly symbol stubs
 *
 * Temporary implementations for assembly symbols until proper
 * assembly files are linked.
 */

#include "types.h"

/* ========================================================================
 * Binary Data Symbols (normally provided by linker scripts)
 * ======================================================================== */

/**
 * Filesystem image (embedded in kernel)
 * TODO: Provide via linker script or objcopy
 */
uint8_t _binary_fs_img_start[4096] __attribute__((aligned(4096))) = {0};
uint64_t _binary_fs_img_size = sizeof(_binary_fs_img_start);

/**
 * Initial process code (first user-space program)
 * TODO: Provide via linker script or objcopy
 */
uint8_t _binary_initcode_start[512] __attribute__((aligned(16))) = {
    /* Simple halt instruction for now */
    0xf4, /* HLT on x86 */
};
uint64_t _binary_initcode_size = sizeof(_binary_initcode_start);

/**
 * Data segment symbol
 * TODO: Provide via linker script
 */
char data[1] __attribute__((section(".data"))) = {0};

/* ========================================================================
 * Interrupt/Trap Vector Table
 * ======================================================================== */

/**
 * Interrupt vector table (256 entries for x86)
 * TODO: Provide proper assembly implementation
 */
void (*vectors[256])(void) = {0};

/**
 * Trap return address
 * TODO: Provide proper assembly implementation
 */
void trapret(void) {
    /* Stub - should be in assembly */
    for(;;);
}
