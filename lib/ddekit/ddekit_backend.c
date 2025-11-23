/**
 * @file ddekit_backend.c
 * @brief DDEKit backend implementation using Exokernel primitives
 *
 * This file implements DDEKit functions using the exov6_interface.h syscalls.
 * It provides memory management, threading, and console output for user-space
 * device drivers.
 */

#include "ddekit.h"
#include "memory.h"
#include "thread.h"
#include "printf.h"
#include "compiler_attrs.h"

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

// Forward declarations from lib/syscall.c
extern uint64_t sys_alloc_page(void);
extern int sys_map_page(int target_env, uint64_t phys, uint64_t virt, int perm);
extern void sys_yield(void);
extern void sys_cputs(const char *s, int len);

// Forward declaration from lib/print.c
extern void print(const char *s);

// ═══════════════════════════════════════════════════════════════════
// Memory Management
// ═══════════════════════════════════════════════════════════════════

// Simple bump allocator for large allocations
#define DDEKIT_HEAP_START 0x50000000ULL
static uint64_t ddekit_heap_ptr = DDEKIT_HEAP_START;

void *ddekit_large_malloc(int size) {
    if (size <= 0)
        return 0;

    // Calculate pages needed
    int pages = (size + EXO_PAGE_SIZE - 1) / EXO_PAGE_SIZE;

    uint64_t start_addr = ddekit_heap_ptr;

    // Allocate and map pages
    for (int i = 0; i < pages; i++) {
        uint64_t phys = sys_alloc_page();
        if (phys == 0 || phys == (uint64_t)-1) {
            // Allocation failed - we can't easily roll back
            return 0;
        }

        // Map with RW permissions (PERM_R=1, PERM_W=2)
        if (sys_map_page(0, phys, ddekit_heap_ptr, 0x3) < 0) {
            return 0;
        }

        ddekit_heap_ptr += EXO_PAGE_SIZE;
    }

    return (void *)start_addr;
}

void ddekit_large_free(void *p) {
    // Simple allocator - no-op for now
    // TODO: Implement proper free with sys_page_unmap
    (void)p;
}

void *ddekit_simple_malloc(unsigned size) {
    // Route to large_malloc for simplicity
    return ddekit_large_malloc((int)size);
}

void ddekit_simple_free(void *p) {
    ddekit_large_free(p);
}

void *ddekit_contig_malloc(unsigned long size, unsigned long low,
                           unsigned long high, unsigned long alignment,
                           unsigned long boundary) {
    // Simplified: ignore alignment constraints for now
    (void)low;
    (void)high;
    (void)alignment;
    (void)boundary;
    return ddekit_large_malloc((int)size);
}

// ═══════════════════════════════════════════════════════════════════
// Slab Allocator (Simplified)
// ═══════════════════════════════════════════════════════════════════

struct ddekit_slab {
    unsigned obj_size;
    int contiguous;
    void *user_data;
    // Simple free list
    void *free_list;
    void *base;
    unsigned capacity;
};

struct ddekit_slab *ddekit_slab_init(unsigned size, int contiguous) {
    struct ddekit_slab *slab = ddekit_simple_malloc(sizeof(struct ddekit_slab));
    if (!slab)
        return 0;

    slab->obj_size = size < sizeof(void *) ? sizeof(void *) : size;
    slab->contiguous = contiguous;
    slab->user_data = 0;
    slab->free_list = 0;

    // Pre-allocate one page worth of objects
    unsigned objs_per_page = EXO_PAGE_SIZE / slab->obj_size;
    slab->capacity = objs_per_page;
    slab->base = ddekit_large_malloc(EXO_PAGE_SIZE);

    if (!slab->base) {
        ddekit_simple_free(slab);
        return 0;
    }

    // Build free list
    char *ptr = (char *)slab->base;
    for (unsigned i = 0; i < objs_per_page - 1; i++) {
        *(void **)(ptr + i * slab->obj_size) = ptr + (i + 1) * slab->obj_size;
    }
    *(void **)(ptr + (objs_per_page - 1) * slab->obj_size) = 0;
    slab->free_list = slab->base;

    return slab;
}

void ddekit_slab_destroy(struct ddekit_slab *slab) {
    if (slab) {
        ddekit_large_free(slab->base);
        ddekit_simple_free(slab);
    }
}

void ddekit_slab_set_data(struct ddekit_slab *slab, void *data) {
    if (slab)
        slab->user_data = data;
}

void *ddekit_slab_get_data(struct ddekit_slab *slab) {
    return slab ? slab->user_data : 0;
}

void *ddekit_slab_alloc(struct ddekit_slab *slab) {
    if (!slab || !slab->free_list)
        return 0;

    void *obj = slab->free_list;
    slab->free_list = *(void **)obj;
    return obj;
}

void ddekit_slab_free(struct ddekit_slab *slab, void *objp) {
    if (!slab || !objp)
        return;

    *(void **)objp = slab->free_list;
    slab->free_list = objp;
}

void ddekit_slab_setup_page_cache(unsigned pages) {
    // Simplified: no page cache management
    (void)pages;
}

// ═══════════════════════════════════════════════════════════════════
// Threading (Stubs - Single-threaded for now)
// ═══════════════════════════════════════════════════════════════════

struct ddekit_thread {
    int id;
    const char *name;
    void (*func)(void *);
    void *arg;
    int started;
};

struct ddekit_thread *ddekit_thread_create(void (*fun)(void *), void *arg,
                                            const char *name) {
    // WARNING: Threading not fully implemented in LibOS yet
    // This creates a stub thread structure
    print("WARNING: ddekit_thread_create not fully implemented.\n");

    struct ddekit_thread *t = ddekit_simple_malloc(sizeof(struct ddekit_thread));
    if (!t)
        return 0;

    t->id = 0;
    t->name = name;
    t->func = fun;
    t->arg = arg;
    t->started = 0;

    // In a real implementation, we would:
    // 1. sys_env_create() to create a new environment
    // 2. Set up the stack and entry point
    // 3. sys_env_run() to start it

    return t;
}

void ddekit_thread_schedule(void) {
    sys_yield();
}

void ddekit_thread_exit(void) {
    // Exit would need SYS_env_destroy
    for (;;)
        sys_yield();
}

void ddekit_thread_msleep(unsigned long msecs) {
    // No timer syscall yet - busy wait
    (void)msecs;
    for (volatile unsigned long i = 0; i < msecs * 1000; i++)
        ;
}

// ═══════════════════════════════════════════════════════════════════
// Console Output
// ═══════════════════════════════════════════════════════════════════

int ddekit_print(const char *str) {
    if (str) {
        int len = 0;
        while (str[len])
            len++;
        sys_cputs(str, len);
        return len;
    }
    return 0;
}

// Simplified printf - just prints format string
// TODO: Implement proper vsnprintf
int ddekit_printf(const char *fmt, ...) {
    int count = 0;
    count += ddekit_print("DDE: ");
    count += ddekit_print(fmt);
    return count;
}

// ═══════════════════════════════════════════════════════════════════
// Initialization
// ═══════════════════════════════════════════════════════════════════

void ddekit_init(void) {
    ddekit_print("DDEKit: Initialized (Exokernel backend)\n");
}
