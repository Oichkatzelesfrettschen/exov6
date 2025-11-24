/**
 * @file umalloc.c
 * @brief User-Space Memory Allocator (Phase 13 - TCC Prerequisites)
 *
 * LIONS' LESSON: A bump allocator is fine for simple programs, but a compiler
 * like TCC needs real malloc/free with memory reclamation.
 *
 * We implement a simple free-list allocator with:
 *   - First-fit allocation strategy
 *   - Coalescing of adjacent free blocks
 *   - 16-byte alignment for all allocations
 *
 * Architecture:
 *   Each block has a header with size and free flag:
 *     struct block_header {
 *         uint64 size;    // Size of usable data (excluding header)
 *         uint64 free;    // 1 if free, 0 if allocated
 *     };
 *
 * The heap grows on-demand by allocating new pages from the kernel.
 */

#include <types.h>
#include <exov6_interface.h>

extern uint64 sys_alloc_page(void);
extern int sys_map_page(int target_env, uint64 phys, uint64 virt, int perm);

/* Heap configuration */
#define HEAP_START      0x40000000ULL
#define PAGE_SIZE       4096
#define MIN_ALLOC_SIZE  16      /* Minimum allocation size (alignment) */
#define HEADER_SIZE     16      /* sizeof(struct block_header) */

/* Block header structure */
struct block_header {
    uint64 size;    /* Size of usable data area (not including header) */
    uint64 free;    /* 1 = free, 0 = allocated */
};

/* Heap state */
static uint64 heap_start = HEAP_START;
static uint64 heap_end = HEAP_START;
static struct block_header *free_list = 0;

/* Round up to nearest multiple of alignment */
static uint64 align_up(uint64 size, uint64 alignment) {
    return (size + alignment - 1) & ~(alignment - 1);
}

/**
 * expand_heap - Allocate more memory from kernel
 *
 * Allocates at least 'needed' bytes by mapping new pages.
 * Returns pointer to new block's header, or 0 on failure.
 */
static struct block_header* expand_heap(uint64 needed) {
    /* Calculate how many pages we need */
    uint64 total_needed = needed + HEADER_SIZE;
    uint64 pages_needed = (total_needed + PAGE_SIZE - 1) / PAGE_SIZE;
    
    struct block_header *new_block = (struct block_header *)heap_end;
    
    /* Allocate and map pages */
    for (uint64 i = 0; i < pages_needed; i++) {
        uint64 phys_addr = sys_alloc_page();
        if (phys_addr == 0) {
            return 0; /* OOM */
        }
        
        uint64 virt_addr = heap_end + (i * PAGE_SIZE);
        if (sys_map_page(0, phys_addr, virt_addr, 0x7) < 0) {
            return 0; /* Mapping failed */
        }
    }
    
    /* Update heap end */
    uint64 new_size = (pages_needed * PAGE_SIZE) - HEADER_SIZE;
    heap_end += pages_needed * PAGE_SIZE;
    
    /* Initialize new block as free */
    new_block->size = new_size;
    new_block->free = 1;
    
    return new_block;
}

/**
 * coalesce - Merge adjacent free blocks
 *
 * LESSON: Fragmentation is the enemy. We combat it by merging adjacent
 * free blocks whenever possible.
 */
static void coalesce(void) {
    if (!free_list) return;
    
    struct block_header *curr = free_list;
    
    while (curr) {
        if (!curr->free) {
            /* Skip to next block */
            uint64 next_addr = (uint64)curr + HEADER_SIZE + curr->size;
            if (next_addr >= heap_end) break;
            curr = (struct block_header *)next_addr;
            continue;
        }
        
        /* Check if next block is also free and adjacent */
        uint64 next_addr = (uint64)curr + HEADER_SIZE + curr->size;
        if (next_addr >= heap_end) break;
        
        struct block_header *next = (struct block_header *)next_addr;
        if (next->free) {
            /* Merge! */
            curr->size += HEADER_SIZE + next->size;
            /* Continue checking from current block */
        } else {
            curr = next;
        }
    }
}

/**
 * malloc - Allocate memory
 */
void* malloc(uint64 size) {
    if (size == 0) return 0;
    
    /* Align size to 16-byte boundary */
    size = align_up(size, MIN_ALLOC_SIZE);
    
    /* Initialize heap on first allocation */
    if (heap_end == heap_start) {
        struct block_header *initial = expand_heap(size);
        if (!initial) return 0;
        free_list = initial;
    }
    
    /* First-fit: search free list for suitable block */
    struct block_header *curr = (struct block_header *)heap_start;
    
    while ((uint64)curr < heap_end) {
        if (curr->free && curr->size >= size) {
            /* Found a suitable block */
            
            /* Split block if it's much larger than needed */
            if (curr->size >= size + HEADER_SIZE + MIN_ALLOC_SIZE) {
                /* Create new free block from remainder */
                uint64 new_block_addr = (uint64)curr + HEADER_SIZE + size;
                struct block_header *new_block = (struct block_header *)new_block_addr;
                new_block->size = curr->size - size - HEADER_SIZE;
                new_block->free = 1;
                
                /* Adjust current block size */
                curr->size = size;
            }
            
            /* Mark block as allocated */
            curr->free = 0;
            
            /* Return pointer to data area (after header) */
            return (void *)((uint64)curr + HEADER_SIZE);
        }
        
        /* Move to next block */
        uint64 next_addr = (uint64)curr + HEADER_SIZE + curr->size;
        if (next_addr >= heap_end) break;
        curr = (struct block_header *)next_addr;
    }
    
    /* No suitable free block found - expand heap */
    struct block_header *new_block = expand_heap(size);
    if (!new_block) return 0;
    
    /* Split if necessary */
    if (new_block->size >= size + HEADER_SIZE + MIN_ALLOC_SIZE) {
        uint64 new_free_addr = (uint64)new_block + HEADER_SIZE + size;
        struct block_header *new_free = (struct block_header *)new_free_addr;
        new_free->size = new_block->size - size - HEADER_SIZE;
        new_free->free = 1;
        new_block->size = size;
    }
    
    new_block->free = 0;
    return (void *)((uint64)new_block + HEADER_SIZE);
}

/**
 * free - Free allocated memory
 */
void free(void* ptr) {
    if (!ptr) return;
    
    /* Get block header */
    struct block_header *block = (struct block_header *)((uint64)ptr - HEADER_SIZE);
    
    /* Validate block is within heap */
    if ((uint64)block < heap_start || (uint64)block >= heap_end) {
        return; /* Invalid pointer */
    }
    
    /* Mark as free */
    block->free = 1;
    
    /* Coalesce adjacent free blocks */
    coalesce();
}

/**
 * calloc - Allocate and zero memory
 */
void* calloc(uint64 nmemb, uint64 size) {
    uint64 total = nmemb * size;
    void *ptr = malloc(total);
    
    if (ptr) {
        /* Zero the memory */
        uint8_t *p = (uint8_t *)ptr;
        for (uint64 i = 0; i < total; i++) {
            p[i] = 0;
        }
    }
    
    return ptr;
}

/**
 * realloc - Resize allocated memory
 */
void* realloc(void* ptr, uint64 size) {
    if (!ptr) return malloc(size);
    if (size == 0) {
        free(ptr);
        return 0;
    }
    
    /* Get old block header */
    struct block_header *old_block = (struct block_header *)((uint64)ptr - HEADER_SIZE);
    
    /* If new size fits in old block, just return it */
    if (old_block->size >= size) {
        return ptr;
    }
    
    /* Allocate new block */
    void *new_ptr = malloc(size);
    if (!new_ptr) return 0;
    
    /* Copy old data */
    uint8_t *src = (uint8_t *)ptr;
    uint8_t *dst = (uint8_t *)new_ptr;
    uint64 copy_size = old_block->size < size ? old_block->size : size;
    for (uint64 i = 0; i < copy_size; i++) {
        dst[i] = src[i];
    }
    
    /* Free old block */
    free(ptr);
    
    return new_ptr;
}
