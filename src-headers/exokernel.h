#pragma once
#include "types.h"
#include "exo.h"
#include "syscall.h"
#include "exo_ipc.h"

/* Capability access rights. */
#define EXO_RIGHT_R 0x1
#define EXO_RIGHT_W 0x2
#define EXO_RIGHT_X 0x4
#define EXO_RIGHT_CTL 0x8

static inline int cap_has_rights(uint rights, uint need) {
  return (rights & need) == need;
}

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
[[nodiscard]] int exo_unbind_page(exo_cap cap);

/* Allocate a disk block capability for device 'dev'.  On success the
 * capability is stored in *cap and zero is returned. */
[[nodiscard]] int exo_alloc_block(uint dev, uint rights, exo_blockcap *cap);

/* Bind the block capability to the buffer 'data'.  If 'write' is non-zero the
 * contents of the buffer are written to disk; otherwise the block is read into
 * the buffer.  Returns 0 on success. */
[[nodiscard]] int exo_bind_block(exo_blockcap *cap, void *data, int write);

/* Allocate a capability referencing an I/O port. */
exo_cap exo_alloc_ioport(uint port);

/* Allocate a capability for an IRQ line. */
exo_cap exo_bind_irq(uint irq);

/* Allocate a DMA buffer page and return a capability for channel 'chan'. */
exo_cap exo_alloc_dma(uint chan);

/* Switch to the context referenced by 'target'.  The caller's context must be
 * saved in a user-managed structure.  The kernel does not choose the next
 * runnable task. */
[[nodiscard]] int exo_yield_to(exo_cap target);

/* Send 'len' bytes from 'buf' to destination capability 'dest'.  Any queuing
 * or flow control is managed in user space. */
[[nodiscard]] enum exo_ipc_status exo_send(exo_cap dest, const void *buf,
                                           uint64 len);

/* Receive up to 'len' bytes from source capability 'src' into 'buf'.  The call
 * blocks according to policy implemented by the library OS. */
[[nodiscard]] enum exo_ipc_status exo_recv(exo_cap src, void *buf, uint64 len);

/* Read or write arbitrary byte ranges using a block capability. */
[[nodiscard]] int exo_read_disk(exo_blockcap cap, void *dst, uint64 off,
                                uint64 n);
[[nodiscard]] int exo_write_disk(exo_blockcap cap, const void *src, uint64 off,
                                 uint64 n);

/* Allocate and wait/acknowledge interrupt events. */
exo_cap exo_alloc_irq(uint irq, uint rights);
[[nodiscard]] int exo_irq_wait(exo_cap cap, uint *irq);
[[nodiscard]] int exo_irq_ack(exo_cap cap);
/* Allocate capabilities for I/O ports, IRQs, and DMA channels. */
exo_cap exo_alloc_ioport(uint port);
exo_cap exo_bind_irq(uint irq);
exo_cap exo_alloc_dma(uint chan);
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
  EXO_SYSCALL_READ_DISK = SYS_exo_read_disk,
  EXO_SYSCALL_WRITE_DISK = SYS_exo_write_disk,
  EXO_SYSCALL_ALLOC_IOPORT = SYS_exo_alloc_ioport,
  EXO_SYSCALL_BIND_IRQ = SYS_exo_bind_irq,
  EXO_SYSCALL_ALLOC_DMA = SYS_exo_alloc_dma,
  EXO_SYSCALL_CAP_INC = SYS_cap_inc,
  EXO_SYSCALL_CAP_DEC = SYS_cap_dec,
  EXO_SYSCALL_IRQ_ALLOC = SYS_exo_irq_alloc,
  EXO_SYSCALL_IRQ_WAIT = SYS_exo_irq_wait,
  EXO_SYSCALL_IRQ_ACK = SYS_exo_irq_ack,
};
