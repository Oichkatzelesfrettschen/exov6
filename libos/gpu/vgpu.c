#include "../../include/gpu/vgpu.h"
#include <stdio.h>
#include <errno.h>

static uint64_t next_dev_addr = 0x10000000;

int vgpu_alloc_dev_mem(uint64_t size, uint64_t *dev_addr) {
    if (!dev_addr) return -EINVAL;
    *dev_addr = next_dev_addr;
    next_dev_addr += (size + 4095) & ~4095;
    return 0;
}

int vgpu_free_dev_mem(uint64_t dev_addr) {
    (void)dev_addr;
    // No-op mock
    return 0;
}

int vgpu_submit(vgpu_cmd_t *cmds, int count) {
    if (!cmds || count <= 0) return -EINVAL;

    for (int i = 0; i < count; i++) {
        // In a real system, write to ring buffer mapped via exo_bind_block
        // Here we just simulate processing
        switch (cmds[i].opcode) {
            case VGPU_CMD_COPY_HOST_TO_DEV:
                // Simulate DMA
                break;
            case VGPU_CMD_COPY_DEV_TO_HOST:
                // Simulate DMA
                break;
            case VGPU_CMD_EXEC_KERNEL:
                // Simulate Execution
                break;
            case VGPU_CMD_BARRIER:
                // Simulate Wait
                break;
            default:
                // Unknown
                break;
        }
    }
    return 0;
}
