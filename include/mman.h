/**
 * @file mman.h
 * @brief Memory Management API (Phase 13 - TCC Prerequisites)
 *
 * Minimal mmap/munmap implementation sufficient for TCC.
 * Provides anonymous memory mapping with configurable permissions.
 */

#ifndef MMAN_H
#define MMAN_H

#include <stdint.h>
#include <types.h>

/* Protection flags */
#define PROT_NONE       0x0     /* No access */
#define PROT_READ       0x1     /* Read access */
#define PROT_WRITE      0x2     /* Write access */
#define PROT_EXEC       0x4     /* Execute access */

/* Mapping flags */
#define MAP_SHARED      0x01    /* Share changes */
#define MAP_PRIVATE     0x02    /* Changes are private */
#define MAP_ANONYMOUS   0x20    /* No file backing */
#define MAP_ANON        MAP_ANONYMOUS

/* Error return value */
#define MAP_FAILED      ((void *)-1)

/**
 * Map memory into address space
 * @param addr    Hint address (ignored in current implementation)
 * @param length  Number of bytes to map (rounded up to page size)
 * @param prot    Protection flags (PROT_READ | PROT_WRITE | PROT_EXEC)
 * @param flags   Mapping flags (must include MAP_ANONYMOUS)
 * @param fd      File descriptor (must be -1 for anonymous mapping)
 * @param offset  File offset (ignored for anonymous mapping)
 * @return Pointer to mapped region, or MAP_FAILED on error
 *
 * Example usage (TCC-style JIT allocation):
 *   void *code = mmap(0, 4096, PROT_READ|PROT_WRITE|PROT_EXEC,
 *                     MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
 *   if (code == MAP_FAILED) { error handling }
 *   // Write JIT code to memory
 *   // Execute it
 */
void* mmap(void* addr, uint64 length, int prot, int flags, int fd, uint64 offset);

/**
 * Unmap memory from address space
 * @param addr    Address of mapped region
 * @param length  Number of bytes to unmap
 * @return 0 on success, -1 on error
 */
int munmap(void* addr, uint64 length);

/**
 * Change protection on memory region
 * @param addr  Address of region
 * @param len   Length of region
 * @param prot  New protection flags
 * @return 0 on success, -1 on error
 */
int mprotect(void* addr, uint64 len, int prot);

#endif /* MMAN_H */
