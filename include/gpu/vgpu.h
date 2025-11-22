#ifndef VGPU_H
#define VGPU_H

#include <stdint.h>

/**
 * @brief Virtual GPU Command Structure
 */
typedef struct vgpu_cmd {
    uint32_t opcode;
    uint32_t flags;
    uint64_t addr;        /* Device Address or Source Address */
    uint64_t size;        /* Size of transfer or execution grid */
    uint64_t args[4];     /* Opcode specific arguments */
} vgpu_cmd_t;

/* Opcodes */
#define VGPU_CMD_NOP               0
#define VGPU_CMD_COPY_HOST_TO_DEV  1
#define VGPU_CMD_COPY_DEV_TO_HOST  2
#define VGPU_CMD_EXEC_KERNEL       3
#define VGPU_CMD_BARRIER           4

/* Flags */
#define VGPU_FLAG_ASYNC            (1 << 0)
#define VGPU_FLAG_SIGNAL_FENCE     (1 << 1)

/**
 * @brief Submit commands to the GPU command queue.
 *
 * @param cmds Array of commands
 * @param count Number of commands
 * @return 0 on success, -1 on error
 */
int vgpu_submit(vgpu_cmd_t *cmds, int count);

/**
 * @brief Allocate memory on the GPU device.
 *
 * @param size Size in bytes
 * @param dev_addr Output pointer for device address
 * @return 0 on success
 */
int vgpu_alloc_dev_mem(uint64_t size, uint64_t *dev_addr);

/**
 * @brief Free device memory.
 */
int vgpu_free_dev_mem(uint64_t dev_addr);

#endif
