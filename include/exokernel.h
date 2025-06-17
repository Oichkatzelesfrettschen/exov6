#pragma once
#include "types.h"
#include "exo.h"
#include "syscall.h"

/* Capability access rights. */
#define EXO_RIGHT_R 0x1
#define EXO_RIGHT_W 0x2
#define EXO_RIGHT_X 0x4
#define EXO_RIGHT_CTL 0x8

static inline int cap_has_rights(uint32_t rights, uint32_t need) {
  return (rights & need) == need;
}

typedef struct {
  exo_cap cap;
} HypervisorCap;

/*
 * Minimal exokernel capability primitives.  Library operating systems
 * build higher level abstractions using only these calls.  The kernel
 * enforces no policy on queue sizes or scheduling.
 */

#ifndef EXO_KERNEL
/* Allocate a physical page and return a capability referencing it.  The page
 * is not mapped into the caller's address space.  On failure a zeroed
 * capability is returned. */
exo_cap exo_alloc_page(void);

/* Free the page referenced by cap and remove any mappings to it.  Returns 0
 * on success and -1 on failure. */
EXO_NODISCARD int exo_unbind_page(exo_cap cap);

/* Allocate a disk block capability for device 'dev'.  On success the
 * capability is stored in *cap and zero is returned. */
EXO_NODISCARD int exo_alloc_block(uint32_t dev, uint32_t rights,
                                  exo_blockcap *cap);

/* Bind the block capability to the buffer 'data'.  If 'write' is non-zero the
 * contents of the buffer are written to disk; otherwise the block is read into
 * the buffer.  Returns 0 on success. */
EXO_NODISCARD int exo_bind_block(exo_blockcap *cap, void *data, int write);

/* Allocate a capability referencing an I/O port. */
exo_cap exo_alloc_ioport(uint32_t port);

/* Allocate a capability for an IRQ line. */
exo_cap exo_bind_irq(uint32_t irq);

/* Allocate a DMA buffer page and return a capability for channel 'chan'. */
exo_cap exo_alloc_dma(uint32_t chan);
HypervisorCap exo_alloc_hypervisor(void);
EXO_NODISCARD int exo_hv_launch(HypervisorCap hv, const char *path);

/* Switch to the context referenced by 'target'.  The caller's context must be
 * saved in a user-managed structure.  The kernel does not choose the next
 * runnable task. */
EXO_NODISCARD int exo_yield_to(exo_cap target);

/* Send 'len' bytes from 'buf' to destination capability 'dest'.  Any queuing
 * or flow control is managed in user space. */
EXO_NODISCARD int exo_send(exo_cap dest, const void *buf, uint64_t len);

/* Receive up to 'len' bytes from source capability 'src' into 'buf'.  The call
 * blocks according to policy implemented by the library OS. */
EXO_NODISCARD int exo_recv(exo_cap src, void *buf, uint64_t len);
EXO_NODISCARD int exo_recv_timed(exo_cap src, void *buf, uint64_t len,
                                 unsigned timeout);

/* Read or write arbitrary byte ranges using a block capability. */
EXO_NODISCARD int exo_read_disk(exo_blockcap cap, void *dst, uint64_t off,
                                uint64_t n);
EXO_NODISCARD int exo_write_disk(exo_blockcap cap, const void *src,
                                 uint64_t off, uint64_t n);

/* Allocate and wait/acknowledge interrupt events. */
exo_cap exo_alloc_irq(uint32_t irq, uint32_t rights);
EXO_NODISCARD int exo_irq_wait(exo_cap cap, uint32_t *irq);
EXO_NODISCARD int exo_irq_ack(exo_cap cap);
#endif /* EXO_KERNEL */

/* Enumeration of syscall numbers for the primitives. */
enum exo_syscall {
  EXO_SYSCALL_ALLOC_PAGE = SYS_exo_alloc_page,
  EXO_SYSCALL_UNBIND_PAGE = SYS_exo_unbind_page,
  EXO_SYSCALL_ALLOC_BLOCK = SYS_exo_alloc_block,
  EXO_SYSCALL_BIND_BLOCK = SYS_exo_bind_block,
  EXO_SYSCALL_FLUSH_BLOCK = SYS_exo_flush_block,
  EXO_SYSCALL_YIELD_TO = SYS_exo_yield_to,
  EXO_SYSCALL_SEND = SYS_exo_send,
  EXO_SYSCALL_RECV = SYS_exo_recv,
  EXO_SYSCALL_RECV_TIMED = SYS_exo_recv_timed,
  EXO_SYSCALL_READ_DISK = SYS_exo_read_disk,
  EXO_SYSCALL_WRITE_DISK = SYS_exo_write_disk,
  EXO_SYSCALL_ALLOC_IOPORT = SYS_exo_alloc_ioport,
  EXO_SYSCALL_BIND_IRQ = SYS_exo_bind_irq,
  EXO_SYSCALL_ALLOC_DMA = SYS_exo_alloc_dma,
  EXO_SYSCALL_ALLOC_HYPERVISOR = SYS_exo_alloc_hypervisor,
  EXO_SYSCALL_HV_LAUNCH = SYS_hv_launch,
  EXO_SYSCALL_CAP_INC = SYS_cap_inc,
  EXO_SYSCALL_CAP_DEC = SYS_cap_dec,
  EXO_SYSCALL_IRQ_ALLOC = SYS_exo_irq_alloc,
  EXO_SYSCALL_IRQ_WAIT = SYS_exo_irq_wait,
  EXO_SYSCALL_IRQ_ACK = SYS_exo_irq_ack,
  EXO_SYSCALL_SERVICE_REGISTER = SYS_service_register,
  EXO_SYSCALL_SERVICE_ADD_DEP = SYS_service_add_dependency,
};
