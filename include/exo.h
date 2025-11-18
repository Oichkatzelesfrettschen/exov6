#ifndef EXOV6_EXO_H
#define EXOV6_EXO_H

/**
 * @file exo.h
 * @brief Unified exokernel interface
 * 
 * Consolidated from kernel/exo.h and include/exo.h
 * Pure C17 implementation
 */

#include <stdint.h>
#include <stddef.h>
#include "types.h"

/* Hash for capability authentication */
typedef struct hash256 {
    uint64_t parts[4];
} hash256_t;

/* Exokernel capability structure */
typedef struct exo_cap {
    uint32_t pa;         /* Physical address (if memory cap) */
    uint32_t id;         /* Resource identifier */
    uint32_t rights;     /* Rights bitmask */
    uint32_t owner;      /* Owner process/zone */
    hash256_t auth_tag;  /* Authentication tag */
} exo_cap;

/* Capability type constants */
#define EXO_CAP_INVALID    0
#define EXO_CAP_PAGE       1
#define EXO_CAP_IRQ        2
#define EXO_CAP_DMA        3
#define EXO_CAP_HYPERVISOR 4
#define EXO_CAP_BLOCK      5
#define EXO_CAP_IOPORT     6

/* Capability rights constants */
#define EXO_CAP_READ       (1 << 0)
#define EXO_CAP_WRITE      (1 << 1)
#define EXO_CAP_EXECUTE    (1 << 2)

/* Legacy aliases for compatibility with kernel code */
#define EXO_RIGHT_R        EXO_CAP_READ
#define EXO_RIGHT_W        EXO_CAP_WRITE
#define EXO_RIGHT_X        EXO_CAP_EXECUTE
#define EXO_RIGHT_EXEC     EXO_CAP_EXECUTE  /* Alternative name */

/* Block device capability */
typedef struct exo_blockcap {
    uint32_t dev;        /* Device number */
    uint32_t blockno;    /* Block number */
    uint32_t rights;     /* Rights bitmask */
    uint32_t owner;      /* Owner process/zone */
} exo_blockcap;

/* Function declarations appropriate for include/ */
int exo_self_insert_pte(uint32_t vaddr, uint32_t pte);
int exo_self_unmap_page(uint32_t vaddr);
int exo_self_insert_pte_range(uint32_t vaddr, uint32_t *pte, size_t count);

/* Capability operations */
int cap_verify(exo_cap c);
exo_cap cap_new(uint32_t id, uint32_t rights, uint32_t owner);

/* IPC operations */
int exo_send(exo_cap dest, const void *msg, uint64_t len);
int exo_recv(exo_cap src, void *msg, uint64_t len);

/* Disk operations */
int exo_disk_read(exo_blockcap cap, void *buf);
int exo_disk_write(exo_blockcap cap, const void *buf);

#ifdef EXO_KERNEL
/* Kernel-only functions */
exo_cap exo_alloc_page(void);
[[nodiscard]] int exo_unbind_page(exo_cap c);

/* Block allocation functions */
exo_blockcap exo_alloc_block(uint32_t dev, uint32_t rights);
int exo_bind_block(exo_blockcap *cap, struct buf *buf, int write);
#endif

#endif /* EXOV6_EXO_H */
