#include <types.h>
#include "param.h"
#include "memlayout.h" 
#include "mmu.h"
#include <arch.h>
#include "spinlock.h"

// Minimal kernel main - replaces kernel_stub.c
// This is the real kernel entry point

// Forward declarations for functions we'll need
void console_init(void);
void memory_init(void);
void process_init(void);

// Simple console output
void kprintf(const char *fmt, ...) {
    // Minimal printf implementation
    const char *p;
    for (p = fmt; *p; p++) {
        if (*p == '%') {
            p++;
            switch (*p) {
                case 's': {
                    // String argument would go here
                    // For now, just skip
                    break;
                }
                case 'd': {
                    // Integer argument would go here  
                    // For now, just skip
                    break;
                }
                default:
                    // Just print the character
                    break;
            }
        } else {
            // Print character directly - this would need actual console driver
            // For now, we'll assume we have some basic output capability
        }
    }
}

// Minimal memory allocator
static char memory_pool[1024 * 1024];  // 1MB static memory pool
static char *next_free = memory_pool;

void* kmalloc(size_t size) {
    if (next_free + size > memory_pool + sizeof(memory_pool)) {
        return 0;  // Out of memory
    }
    char *ptr = next_free;
    next_free += size;
    return ptr;
}

void kfree(void *ptr) {
    // Simple allocator - no free for now
    (void)ptr;
}

// Minimal process structure
struct proc {
    int pid;
    int state;
    char name[16];
};

static struct proc proc_table[64];
static int next_pid = 1;

struct proc* allocproc(void) {
    for (int i = 0; i < 64; i++) {
        if (proc_table[i].state == 0) {  // UNUSED
            proc_table[i].pid = next_pid++;
            proc_table[i].state = 1;     // EMBRYO
            return &proc_table[i];
        }
    }
    return 0;  // No free proc
}

// Kernel main function - called from bootloader
void kmain(void) {
    // Initialize core systems
    kprintf("ExoKernel v6 starting...\n");
    
    // Initialize memory management
    memory_init();
    kprintf("Memory initialized\n");
    
    // Initialize processes
    process_init();
    kprintf("Process system initialized\n");
    
    // Initialize console
    console_init();
    kprintf("Console initialized\n");
    
    kprintf("ExoKernel v6 ready!\n");
    
    // Create first user process
    struct proc *p = allocproc();
    if (p) {
        // Set up first process
        p->state = 2;  // RUNNABLE
        kprintf("First process created (PID %d)\n", p->pid);
        
        // Copy process name
        for (int i = 0; i < 15; i++) {
            p->name[i] = "init"[i];
            if (p->name[i] == 0) break;
        }
        p->name[15] = 0;
    }
    
    // Enter scheduler loop
    kprintf("Starting scheduler...\n");
    scheduler();
}

// Basic implementations of required functions
void memory_init(void) {
    // Initialize our simple memory allocator
    next_free = memory_pool;
    kprintf("Memory pool: %p - %p (%d bytes)\n", 
           memory_pool, memory_pool + sizeof(memory_pool), 
           (int)sizeof(memory_pool));
}

void process_init(void) {
    // Clear process table
    for (int i = 0; i < 64; i++) {
        proc_table[i].state = 0;  // UNUSED
        proc_table[i].pid = 0;
        for (int j = 0; j < 16; j++) {
            proc_table[i].name[j] = 0;
        }
    }
    kprintf("Process table initialized (64 entries)\n");
}

void console_init(void) {
    // Initialize console/serial output
    // For now, this is a stub
    kprintf("Console driver loaded\n");
}

// Simple round-robin scheduler
void scheduler(void) {
    struct proc *p;
    int current = 0;
    
    kprintf("Scheduler started\n");
    
    for (;;) {
        // Find next runnable process
        for (int i = 0; i < 64; i++) {
            p = &proc_table[current];
            current = (current + 1) % 64;
            
            if (p->state == 2) {  // RUNNABLE
                // Run this process
                kprintf("Running process %d (%s)\n", p->pid, p->name);
                
                // Simulate process execution
                // In real kernel, this would switch to user mode
                // For now, just print and continue
                
                // Yield after some time
                break;
            }
        }
        
        // Yield CPU - in real kernel this would be a proper yield
        // For now, just continue the loop
    }
}

// Panic function for errors
void panic(const char *s) {
    kprintf("KERNEL PANIC: %s\n", s);
    for (;;) {
        // Halt the system
#ifdef __x86_64__
        __asm__ volatile("hlt");
#elif defined(__aarch64__)
        __asm__ volatile("wfi");
#else
        // Generic halt
        while(1);
#endif
    }
}