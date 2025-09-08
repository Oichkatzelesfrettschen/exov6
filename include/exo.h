<<<<<<< HEAD
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

#endif /* EXOV6_EXO_H */
=======
#ifndef EXO_H
#define EXO_H
#include "types.h"

typedef struct hash256 {
  uint64_t parts[4];
} hash256_t;

typedef struct exo_cap {
  uint32_t pa;
  uint32_t id;
  uint32_t rights;
  uint32_t owner;
  hash256_t auth_tag;
} exo_cap;

typedef struct exo_blockcap {
  uint32_t dev;
  uint32_t blockno;
  uint32_t rights;
  uint32_t owner;
} exo_blockcap;

#ifdef EXO_KERNEL
exo_cap exo_alloc_page(void);
[[nodiscard]] int exo_unbind_page(exo_cap c);
exo_cap cap_new(uint32_t id, uint32_t rights, uint32_t owner);
int cap_verify(exo_cap c);
#endif

#endif /* EXO_H */
>>>>>>> e875b0d46288791972060b75ca2e13af06f63771
