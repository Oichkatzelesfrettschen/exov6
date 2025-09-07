/**
 * memory.c - POSIX memory management for FeuerBird exokernel
 * 
 * Implements mmap, munmap, mprotect, and related functions
 * using exokernel capabilities for memory management.
 */

#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include <arch.h>
#include "libos/posix.h"
#include "exo.h"
#include "errno.h"
#include <stddef.h>
#include <stdlib.h>
#include <sys/mman.h>

// Memory region tracking
typedef struct mem_region {
    void *addr;
    size_t len;
    int prot;
    int flags;
    int fd;
    off_t offset;
    exo_cap mem_cap;
    struct mem_region *next;
} mem_region_t;

static mem_region_t *mem_regions = NULL;
static int mem_initialized = 0;

// Initialize memory management
static void
init_memory_management(void)
{
    if (mem_initialized)
        return;
    
    mem_regions = NULL;
    mem_initialized = 1;
}

// Find a memory region by address
static mem_region_t *
find_region(void *addr)
{
    mem_region_t *r;
    
    for (r = mem_regions; r != NULL; r = r->next) {
        if (r->addr <= addr && 
            (char *)r->addr + r->len > (char *)addr) {
            return r;
        }
    }
    return NULL;
}

// Allocate virtual address space
static void *
allocate_virtual_space(size_t len)
{
    // In a real implementation, this would:
    // 1. Find a free virtual address range
    // 2. Reserve it in the process's address space
    // 3. Return the base address
    
    // For now, use a simple allocator
    static char *next_addr = (char *)0x40000000;  // User space start
    void *addr = next_addr;
    next_addr += PGROUNDUP(len);
    
    if ((uintptr_t)next_addr > 0x80000000) {  // User space limit
        return NULL;
    }
    
    return addr;
}

/**
 * mmap - Map files or devices into memory
 * 
 * @addr: Suggested address (or NULL)
 * @len: Length of mapping
 * @prot: Memory protection flags
 * @flags: Mapping flags
 * @fd: File descriptor (or -1 for anonymous)
 * @offset: Offset in file
 * 
 * Returns mapped address on success, MAP_FAILED on error
 */
void *
libos_mmap(void *addr, size_t len, int prot, int flags, int fd, off_t offset)
{
    mem_region_t *region;
    exo_cap mem_cap;
    void *mapped_addr;
    
    init_memory_management();
    
    // Validate parameters
    if (len == 0) {
        errno = EINVAL;
        return MAP_FAILED;
    }
    
    // Align length to page boundary
    len = PGROUNDUP(len);
    
    // Handle address hint
    if (addr != NULL) {
        // Check if address is page-aligned
        if ((uintptr_t)addr & (PGSIZE - 1)) {
            if (flags & MAP_FIXED) {
                errno = EINVAL;
                return MAP_FAILED;
            }
            addr = NULL;  // Ignore unaligned hint
        }
        
        // Check if region is already mapped (for MAP_FIXED)
        if (flags & MAP_FIXED) {
            mem_region_t *existing = find_region(addr);
            if (existing != NULL) {
                // Unmap existing region first
                if (libos_munmap(addr, len) < 0) {
                    return MAP_FAILED;
                }
            }
        }
    }
    
    // Allocate virtual address space
    if (addr == NULL || !(flags & MAP_FIXED)) {
        mapped_addr = allocate_virtual_space(len);
        if (mapped_addr == NULL) {
            errno = ENOMEM;
            return MAP_FAILED;
        }
    } else {
        mapped_addr = addr;
    }
    
    // Set protection flags
    uint32_t exo_prot = 0;
    if (prot & PROT_READ)  exo_prot |= EXO_PROT_READ;
    if (prot & PROT_WRITE) exo_prot |= EXO_PROT_WRITE;
    if (prot & PROT_EXEC)  exo_prot |= EXO_PROT_EXEC;
    
    // Request memory capability from exokernel
    mem_cap = exo_request_memory(len, exo_prot);
    if (mem_cap.id == 0) {
        errno = ENOMEM;
        return MAP_FAILED;
    }
    
    // Map capability to virtual address
    if (exo_map_capability(mem_cap, mapped_addr, len, exo_prot) == NULL) {
        exo_release_capability(mem_cap);
        errno = ENOMEM;
        return MAP_FAILED;
    }
    
    // Handle file-backed mapping
    if (fd >= 0 && !(flags & MAP_ANONYMOUS)) {
        exo_cap file_cap = fd_to_capability(fd);
        if (file_cap.id == 0) {
            exo_unmap_capability(mem_cap, mapped_addr);
            exo_release_capability(mem_cap);
            errno = EBADF;
            return MAP_FAILED;
        }
        
        // Bind memory to file
        if (exo_bind_memory_file(mem_cap, file_cap, offset) < 0) {
            exo_unmap_capability(mem_cap, mapped_addr);
            exo_release_capability(mem_cap);
            errno = EIO;
            return MAP_FAILED;
        }
    }
    
    // Create region tracking structure
    region = (mem_region_t *)malloc(sizeof(mem_region_t));
    if (region == NULL) {
        exo_unmap_capability(mem_cap, mapped_addr);
        exo_release_capability(mem_cap);
        errno = ENOMEM;
        return MAP_FAILED;
    }
    
    region->addr = mapped_addr;
    region->len = len;
    region->prot = prot;
    region->flags = flags;
    region->fd = fd;
    region->offset = offset;
    region->mem_cap = mem_cap;
    
    // Add to region list
    region->next = mem_regions;
    mem_regions = region;
    
    return mapped_addr;
}

/**
 * munmap - Unmap memory region
 * 
 * @addr: Address of mapping
 * @len: Length to unmap
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_munmap(void *addr, size_t len)
{
    mem_region_t *region, *prev = NULL;
    
    init_memory_management();
    
    // Validate parameters
    if (addr == NULL || len == 0) {
        errno = EINVAL;
        return -1;
    }
    
    // Check alignment
    if ((uintptr_t)addr & (PGSIZE - 1)) {
        errno = EINVAL;
        return -1;
    }
    
    // Align length
    len = PGROUNDUP(len);
    
    // Find and remove region
    for (region = mem_regions; region != NULL; prev = region, region = region->next) {
        if (region->addr == addr) {
            // Check if we're unmapping the whole region or part
            if (region->len != len) {
                // Partial unmapping not yet supported
                errno = EINVAL;
                return -1;
            }
            
            // Unmap from virtual address space
            if (exo_unmap_capability(region->mem_cap, addr) < 0) {
                errno = EINVAL;
                return -1;
            }
            
            // Release capability
            exo_release_capability(region->mem_cap);
            
            // Remove from list
            if (prev)
                prev->next = region->next;
            else
                mem_regions = region->next;
            
            free(region);
            return 0;
        }
    }
    
    errno = EINVAL;
    return -1;
}

/**
 * mprotect - Set protection on memory region
 * 
 * @addr: Address of region
 * @len: Length of region
 * @prot: New protection flags
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_mprotect(void *addr, size_t len, int prot)
{
    mem_region_t *region;
    uint32_t exo_prot = 0;
    
    init_memory_management();
    
    // Validate parameters
    if (addr == NULL || len == 0) {
        errno = EINVAL;
        return -1;
    }
    
    // Check alignment
    if ((uintptr_t)addr & (PGSIZE - 1)) {
        errno = EINVAL;
        return -1;
    }
    
    // Find region
    region = find_region(addr);
    if (region == NULL) {
        errno = ENOMEM;
        return -1;
    }
    
    // Convert protection flags
    if (prot & PROT_READ)  exo_prot |= EXO_PROT_READ;
    if (prot & PROT_WRITE) exo_prot |= EXO_PROT_WRITE;
    if (prot & PROT_EXEC)  exo_prot |= EXO_PROT_EXEC;
    
    // Update protection
    if (exo_set_protection(region->mem_cap, exo_prot) < 0) {
        errno = EACCES;
        return -1;
    }
    
    region->prot = prot;
    return 0;
}

/**
 * msync - Synchronize memory with storage
 * 
 * @addr: Address of region
 * @len: Length to sync
 * @flags: Sync flags
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_msync(void *addr, size_t len, int flags)
{
    mem_region_t *region;
    
    init_memory_management();
    
    // Validate parameters
    if (addr == NULL || len == 0) {
        errno = EINVAL;
        return -1;
    }
    
    // Find region
    region = find_region(addr);
    if (region == NULL) {
        errno = ENOMEM;
        return -1;
    }
    
    // Check if file-backed
    if (region->fd < 0) {
        // Anonymous mapping, nothing to sync
        return 0;
    }
    
    // Sync to storage
    if (exo_sync_memory(region->mem_cap, flags & MS_ASYNC) < 0) {
        errno = EIO;
        return -1;
    }
    
    return 0;
}

/**
 * mlock - Lock memory pages
 * 
 * @addr: Address to lock
 * @len: Length to lock
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_mlock(const void *addr, size_t len)
{
    mem_region_t *region;
    
    init_memory_management();
    
    // Find region
    region = find_region((void *)addr);
    if (region == NULL) {
        errno = ENOMEM;
        return -1;
    }
    
    // Lock pages
    if (exo_lock_memory(region->mem_cap, addr, len) < 0) {
        errno = EPERM;
        return -1;
    }
    
    return 0;
}

/**
 * munlock - Unlock memory pages
 * 
 * @addr: Address to unlock
 * @len: Length to unlock
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_munlock(const void *addr, size_t len)
{
    mem_region_t *region;
    
    init_memory_management();
    
    // Find region
    region = find_region((void *)addr);
    if (region == NULL) {
        errno = ENOMEM;
        return -1;
    }
    
    // Unlock pages
    if (exo_unlock_memory(region->mem_cap, addr, len) < 0) {
        errno = EPERM;
        return -1;
    }
    
    return 0;
}

/**
 * brk - Change data segment size
 * 
 * @addr: New break address
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_brk(void *addr)
{
    static void *current_brk = NULL;
    static mem_region_t *heap_region = NULL;
    
    init_memory_management();
    
    // Initialize heap on first call
    if (current_brk == NULL) {
        current_brk = (void *)0x50000000;  // Heap start
        
        // Allocate initial heap
        size_t initial_size = 0x10000;  // 64KB
        void *heap = libos_mmap(current_brk, initial_size,
                                PROT_READ | PROT_WRITE,
                                MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED,
                                -1, 0);
        if (heap == MAP_FAILED) {
            return -1;
        }
        
        heap_region = find_region(current_brk);
        current_brk = (char *)current_brk + initial_size;
    }
    
    // Adjust heap size
    if (addr > current_brk) {
        // Expand heap
        size_t expand_size = (char *)addr - (char *)current_brk;
        void *new_area = libos_mmap(current_brk, expand_size,
                                    PROT_READ | PROT_WRITE,
                                    MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED,
                                    -1, 0);
        if (new_area == MAP_FAILED) {
            errno = ENOMEM;
            return -1;
        }
    } else if (addr < current_brk) {
        // Shrink heap
        size_t shrink_size = (char *)current_brk - (char *)addr;
        if (libos_munmap(addr, shrink_size) < 0) {
            return -1;
        }
    }
    
    current_brk = addr;
    return 0;
}

/**
 * sbrk - Increment data segment size
 * 
 * @increment: Bytes to add (can be negative)
 * 
 * Returns previous break on success, (void *)-1 on error
 */
void *
libos_sbrk(intptr_t increment)
{
    static void *current_brk = NULL;
    void *old_brk;
    
    // Initialize if needed
    if (current_brk == NULL) {
        if (libos_brk((void *)0x50000000) < 0) {
            return (void *)-1;
        }
        current_brk = (void *)0x50000000;
    }
    
    old_brk = current_brk;
    
    if (increment != 0) {
        void *new_brk = (char *)current_brk + increment;
        if (libos_brk(new_brk) < 0) {
            return (void *)-1;
        }
        current_brk = new_brk;
    }
    
    return old_brk;
}