/**
 * @file mmap.c
 * @brief Simple mmap/munmap Implementation for TCC (Phase 13)
 *
 * LIONS' LESSON: TCC uses mmap for allocating executable memory for JIT.
 * In a traditional UNIX, mmap is a complex syscall with many features.
 * In ExoV6, we provide a minimal implementation sufficient for TCC.
 *
 * What TCC needs:
 *   - Anonymous memory allocation (MAP_ANONYMOUS)
 *   - Executable memory (PROT_EXEC)
 *   - No file backing (fd = -1)
 *
 * We implement this by allocating pages directly from the kernel
 * and mapping them with appropriate permissions.
 */

#include <types.h>
#include <exov6_interface.h>

/* mmap flags (subset needed for TCC) */
#define MAP_PRIVATE     0x02    /* Changes are private */
#define MAP_ANONYMOUS   0x20    /* No file backing */
#define MAP_ANON        MAP_ANONYMOUS

/* Protection flags */
#define PROT_NONE       0x0     /* No access */
#define PROT_READ       0x1     /* Read access */
#define PROT_WRITE      0x2     /* Write access */
#define PROT_EXEC       0x4     /* Execute access */

/* mmap error return value */
#define MAP_FAILED      ((void *)-1)

/* External kernel interface */
extern uint64 sys_page_alloc_raw(void);
extern int sys_page_map_raw(int target_env, uint64 phys, uint64 virt, int perm);

/* Simple mmap region allocator */
#define MMAP_START      0x50000000ULL   /* Start of mmap region */
#define MMAP_END        0x60000000ULL   /* End of mmap region */
#define PAGE_SIZE       4096

static uint64 mmap_next_addr = MMAP_START;

/**
 * mmap - Map memory (simplified for TCC)
 *
 * @param addr    Hint address (ignored in our implementation)
 * @param length  Number of bytes to map
 * @param prot    Protection flags (PROT_READ | PROT_WRITE | PROT_EXEC)
 * @param flags   Mapping flags (must include MAP_ANONYMOUS for us)
 * @param fd      File descriptor (must be -1 for anonymous mapping)
 * @param offset  File offset (ignored for anonymous mapping)
 *
 * @return Pointer to mapped region, or MAP_FAILED on error
 *
 * LESSON: We only support anonymous mappings (no file backing).
 * This is sufficient for TCC which uses mmap for allocating
 * executable memory for its JIT compiler.
 */
void* mmap(void* addr, uint64 length, int prot, int flags, int fd, uint64 offset) {
    (void)addr;     /* We ignore address hints */
    (void)offset;   /* Anonymous mapping has no offset */

    /* Validate parameters */
    if (length == 0) {
        return MAP_FAILED;
    }

    /* We only support anonymous mappings */
    if (!(flags & MAP_ANONYMOUS)) {
        return MAP_FAILED;
    }

    /* For anonymous mappings, fd must be -1 */
    if ((flags & MAP_ANONYMOUS) && fd != -1) {
        return MAP_FAILED;
    }

    /* Calculate number of pages needed */
    uint64 pages_needed = (length + PAGE_SIZE - 1) / PAGE_SIZE;
    
    /* Check if we have space */
    if (mmap_next_addr + (pages_needed * PAGE_SIZE) > MMAP_END) {
        return MAP_FAILED;  /* Out of address space */
    }

    /* Convert protection flags to kernel permission bits */
    int kernel_perm = 0;
    if (prot & PROT_READ)  kernel_perm |= 0x1;  /* PERM_R */
    if (prot & PROT_WRITE) kernel_perm |= 0x2;  /* PERM_W */
    if (prot & PROT_EXEC)  kernel_perm |= 0x4;  /* PERM_X */

    /* If no permissions specified, default to read-only */
    if (kernel_perm == 0) {
        kernel_perm = 0x1;
    }

    /* Allocate virtual address */
    uint64 virt_addr = mmap_next_addr;
    mmap_next_addr += pages_needed * PAGE_SIZE;

    /* Allocate and map physical pages */
    for (uint64 i = 0; i < pages_needed; i++) {
        uint64 phys_addr = sys_page_alloc_raw();
        if (phys_addr == 0) {
            /* OOM - would need to unmap already-mapped pages */
            /* For simplicity, we leave them mapped (leak) */
            return MAP_FAILED;
        }

        uint64 page_virt = virt_addr + (i * PAGE_SIZE);
        if (sys_page_map_raw(0, phys_addr, page_virt, kernel_perm) < 0) {
            /* Mapping failed */
            return MAP_FAILED;
        }
    }

    /* Zero the memory (POSIX requirement for anonymous mappings) */
    uint8_t *p = (uint8_t *)virt_addr;
    for (uint64 i = 0; i < pages_needed * PAGE_SIZE; i++) {
        p[i] = 0;
    }

    return (void *)virt_addr;
}

/**
 * munmap - Unmap memory
 *
 * @param addr    Address of mapped region
 * @param length  Number of bytes to unmap
 *
 * @return 0 on success, -1 on error
 *
 * LESSON: In a full implementation, we'd need to:
 *   1. Validate the address is in mmap region
 *   2. Unmap the pages from the page table
 *   3. Return physical pages to the kernel
 *
 * For Phase 13, we provide a stub implementation.
 */
int munmap(void* addr, uint64 length) {
    (void)addr;
    (void)length;
    
    /* 
     * TODO: Implement actual unmapping
     * For now, we just leak the memory. This is acceptable for TCC
     * which typically doesn't munmap its JIT code.
     */
    return 0;
}

/**
 * mprotect - Change protection on memory region
 *
 * @param addr  Address of region
 * @param len   Length of region
 * @param prot  New protection flags
 *
 * @return 0 on success, -1 on error
 *
 * LESSON: TCC may use this to make code pages executable after
 * writing the JIT'd code. For Phase 13, we provide a stub.
 */
int mprotect(void* addr, uint64 len, int prot) {
    (void)addr;
    (void)len;
    (void)prot;
    
    /*
     * TODO: Would need to modify page table permissions
     * For now, we return success assuming pages were already
     * mapped with correct permissions.
     */
    return 0;
}
