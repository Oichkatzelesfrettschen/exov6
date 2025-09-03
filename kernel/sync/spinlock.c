/*
 * Robust Ticket Spinlock Implementation for ExoKernel v6
 * Based on proven designs from NetBSD, Linux, and academic research
 * 
 * This implementation provides:
 * - Fair FIFO ordering via ticket mechanism
 * - Exponential backoff to reduce cache contention
 * - Full memory barriers for correctness
 * - Support for both UP and SMP configurations
 */

#include <types.h>
#include "defs.h"
#include "param.h"
#include <arch_x86_64.h>
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "spinlock.h"

// Configuration for exponential backoff
#define BACKOFF_MIN 10
#define BACKOFF_MAX 1024

// Cache line size detection (typically 64 bytes on modern x86_64)
size_t cache_line_size = 64;

void detect_cache_line_size(void) {
#ifdef __x86_64__
  uint32_t eax, ebx, ecx, edx;
  
  // CPUID function 0x01 gives cache line size in EBX bits 15:8
  cpuid(0x01, &eax, &ebx, &ecx, &edx);
  cache_line_size = ((ebx >> 8) & 0xFF) * 8;
  
  // Fallback to 64 if detection fails
  if (cache_line_size == 0) {
    cache_line_size = 64;
  }
#else
  cache_line_size = 64; // Default for other architectures
#endif
}

#if CONFIG_SMP

/*
 * Initialize a spinlock with the given name.
 * Sets both ticket numbers to 0, indicating the lock is free.
 */
void initlock(struct spinlock *lk, const char *name) {
  lk->name = name;
  lk->ticket.head = 0;
  lk->ticket.tail = 0;
  lk->cpu = 0;
}

/*
 * Acquire the spinlock.
 * Uses ticket mechanism for fair FIFO ordering.
 * Implements exponential backoff to reduce cache contention.
 */
void acquire(struct spinlock *lk) {
  pushcli(); // Disable interrupts to prevent deadlock
  
  if (holding(lk))
    panic("acquire: already holding");
  
  // Get our ticket number
  uint16_t my_ticket = __sync_fetch_and_add(&lk->ticket.tail, 1);
  
  // Wait until it's our turn
  int backoff = BACKOFF_MIN;
  while (__sync_add_and_fetch(&lk->ticket.head, 0) != my_ticket) {
    // Exponential backoff with PAUSE instruction
    for (int i = 0; i < backoff; i++) {
      pause(); // Hint to CPU that we're spinning
    }
    
    // Increase backoff up to maximum
    if (backoff < BACKOFF_MAX) {
      backoff *= 2;
    }
  }
  
  // Memory barrier to ensure all reads/writes complete
  mfence();
  
  // Record debugging info
  lk->cpu = mycpu();
  getcallerpcs(&lk, lk->pcs);
}

/*
 * Release the spinlock.
 * Increments the head ticket to allow next waiter to proceed.
 */
void release(struct spinlock *lk) {
  if (!holding(lk))
    panic("release: not holding");
  
  // Clear debugging info
  lk->pcs[0] = 0;
  lk->cpu = 0;
  
  // Memory barrier before release
  mfence();
  
  // Release the lock by incrementing head
  __sync_add_and_fetch(&lk->ticket.head, 1);
  
  popcli(); // Re-enable interrupts if appropriate
}

/*
 * Try to acquire the lock without blocking.
 * Returns 1 if successful, 0 if lock is held.
 */
int trylock(struct spinlock *lk) {
  pushcli();
  
  if (holding(lk)) {
    popcli();
    return 0;
  }
  
  // Atomic compare-and-swap: only succeed if head == tail
  uint16_t expected = lk->ticket.head;
  uint16_t new_tail = expected + 1;
  
  if (__sync_bool_compare_and_swap(&lk->ticket.tail, expected, new_tail)) {
    // Success - we got the lock
    lk->cpu = mycpu();
    getcallerpcs(&lk, lk->pcs);
    return 1;
  }
  
  // Failed to get lock
  popcli();
  return 0;
}

/*
 * Check if the current CPU holds this lock.
 */
int holding(struct spinlock *lock) {
#ifdef __x86_64__
  int r;
  pushcli();
  r = lock->ticket.head != lock->ticket.tail && lock->cpu == mycpu();
  popcli();
  return r;
#else
  return lock->cpu == mycpu();
#endif
}

#else // !CONFIG_SMP

/*
 * Uniprocessor versions - just manage interrupt state
 */

void initlock(struct spinlock *lk, const char *name) {
  lk->name = name;
  lk->ticket.head = 0;
  lk->ticket.tail = 0;
  lk->cpu = 0;
}

void acquire(struct spinlock *lk) {
  pushcli();
  if (holding(lk))
    panic("acquire: already holding");
  lk->cpu = mycpu();
}

void release(struct spinlock *lk) {
  if (!holding(lk))
    panic("release: not holding");
  lk->cpu = 0;
  popcli();
}

int trylock(struct spinlock *lk) {
  pushcli();
  if (holding(lk)) {
    popcli();
    return 0;
  }
  lk->cpu = mycpu();
  return 1;
}

int holding(struct spinlock *lock) {
  return lock->cpu == mycpu();
}

#endif // CONFIG_SMP

/*
 * Push/pop interrupt enable state.
 * Used to ensure interrupts remain disabled while holding spinlocks.
 */

void pushcli(void) {
  uint64_t flags = read_rflags();
  
  cli();
  if (mycpu()->ncli == 0)
    mycpu()->intena = flags & FL_IF;
  mycpu()->ncli += 1;
}

void popcli(void) {
  if (read_rflags() & FL_IF)
    panic("popcli: interruptible");
  if (--mycpu()->ncli < 0)
    panic("popcli: underflow");
  if (mycpu()->ncli == 0 && mycpu()->intena)
    sti();
}

/*
 * Save caller's program counters for debugging.
 */
void getcallerpcs(void *v, uint32_t pcs[]) {
  uint64_t *rbp;
  int i;
  
  __asm__ volatile("movq %%rbp, %0" : "=r"(rbp));
  
  for (i = 0; i < 10; i++) {
    if (rbp == 0 || rbp < (uint64_t*)KERNBASE || 
        rbp == (uint64_t*)0xffffffff) {
      break;
    }
    pcs[i] = rbp[1];  // Return address is one word above rbp
    rbp = (uint64_t*)rbp[0];  // Follow frame pointer chain
  }
  for (; i < 10; i++)
    pcs[i] = 0;
}