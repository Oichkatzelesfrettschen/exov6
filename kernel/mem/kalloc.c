// kernel/mem/kalloc.c
#include <types.h>
#include <defs.h>
#include <param.h>
#include <memlayout.h>
#include <spinlock.h>
#include "mm.h"
#include <string.h> // for memset

struct {
  struct spinlock lock;
  struct PageInfo *freelist; // Points to the first free PageInfo struct
  uint64 free_pages_count;
} kmem;

// The Global Core Map
struct PageInfo *pages;
uint64 npages; // Total physical pages

extern char end[]; // defined by kernel.ld

void
kinit()
{
  initlock(&kmem.lock, "kmem");

  // 1. Calculate available RAM
  // PHYSTOP is usually 128MB in QEMU xv6
  uint64 mem_size = PHYSTOP - KERNBASE;
  npages = mem_size / PGSIZE;

  // 2. Place the 'pages' array right after the kernel code (at 'end')
  // We need to be careful about alignment.
  pages = (struct PageInfo*) PGROUNDUP((uint64)end);

  // 3. Calculate where free memory ACTUALLY starts
  // It starts after the kernel code + the size of the pages array
  uint64 free_mem_start = PGROUNDUP((uint64)pages + (sizeof(struct PageInfo) * npages));

  cprintf("Exov6 Memory Init: %d pages. Core Map at %p.\n", npages, pages);

  // 4. Initialize the free list
  // We iterate backwards so the free list is in order (optional but nice)
  acquire(&kmem.lock);
  for(uint64 pa = free_mem_start; pa < PHYSTOP; pa += PGSIZE){
      struct PageInfo *pp = PA2PAGE(pa);
      pp->ref_count = 0;
      pp->label = LABEL_LOW; // Default label
      pp->next = kmem.freelist;
      kmem.freelist = pp;
      kmem.free_pages_count++;
  }
  release(&kmem.lock);
}

// Allocate a physical page.
// Returns a kernel VIRTUAL address (void*), just like standard xv6.
// But internally, it updates the PageInfo.
void*
kalloc(void)
{
  struct PageInfo *pp;

  acquire(&kmem.lock);
  pp = kmem.freelist;
  if(pp){
    kmem.freelist = pp->next;
    kmem.free_pages_count--;

    // CRITICAL INITIALIZATION
    pp->next = 0;
    pp->ref_count = 0; // Caller must increment this!
    pp->owner_env = 0; // Caller must set this!
    pp->label = LABEL_LOW; // Caller must set this!
  }
  release(&kmem.lock);

  if(pp == 0)
    return 0;

  // Convert PageInfo back to kernel virtual address to zero it out
  uint64 pa = PAGE2PA(pp);
  char *v = (char*)pa; // In xv6, PA == VA for kernel (mostly)
  memset(v, 0, PGSIZE);
  return (void*)v;
}

// Free a page.
// DECREMENTS ref_count. Only puts on free list if ref_count == 0.
void
kfree(void *pa)
{
  struct PageInfo *pp;

  if(((uint64)pa % PGSIZE) != 0 || (char*)pa < end || (uint64)pa >= PHYSTOP)
    panic("kfree");

  pp = PA2PAGE(pa);

  acquire(&kmem.lock);

  if(pp->ref_count > 0) {
      pp->ref_count--;
  }

  // Only free if no one is using it
  if (pp->ref_count == 0) {
      // Fill with junk to catch dangling refs
      memset(pa, 1, PGSIZE);

      pp->next = kmem.freelist;
      kmem.freelist = pp;
      kmem.free_pages_count++;
  }

  release(&kmem.lock);
}

// Increase reference count (used when mapping a page to a new Env)
void
page_incref(uint64 pa)
{
    acquire(&kmem.lock);
    struct PageInfo *pp = PA2PAGE(pa);
    pp->ref_count++;
    release(&kmem.lock);
}

// Decrease reference count (wrapper for kfree)
void
page_decref(uint64 pa)
{
    kfree((void*)pa);
}

// Get the security label of a physical page
label_t
page_get_label(uint64 pa)
{
    // No lock needed for read (usually), but safer with lock if labels change
    struct PageInfo *pp = PA2PAGE(pa);
    return pp->label;
}

// Set the security label (Privileged Kernel Only)
void
page_set_label(uint64 pa, label_t new_label)
{
    acquire(&kmem.lock);
    struct PageInfo *pp = PA2PAGE(pa);
    pp->label = new_label;
    release(&kmem.lock);
}
