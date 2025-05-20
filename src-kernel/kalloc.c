// Physical memory allocator, intended to allocate
// memory for user processes, kernel stacks, page table pages,
// and pipe buffers. Allocates 4096-byte pages.

#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "spinlock.h"
#include "proc.h"

void freerange(void *vstart, void *vend);
extern char end[]; // first address after kernel loaded from ELF file
                   // defined by the kernel linker script in kernel.ld

struct run {
  struct run *next;
};

static inline int
node_of(uintptr_t pa)
{
  return (pa / PGSIZE) % NNODES;
}

struct {
  struct spinlock lock[NNODES];
  int use_lock;
  struct run *freelist[NNODES];
} kmem;

// Initialization happens in two phases.
// 1. main() calls kinit1() while still using entrypgdir to place just
// the pages mapped by entrypgdir on free list.
// 2. main() calls kinit2() with the rest of the physical pages
// after installing a full page table that maps them on all cores.
void
kinit1(void *vstart, void *vend)
{
  for(int i=0;i<NNODES;i++)
    initlock(&kmem.lock[i], "kmem");
  kmem.use_lock = 0;
  freerange(vstart, vend);
}

void
kinit2(void *vstart, void *vend)
{
  freerange(vstart, vend);
  kmem.use_lock = 1;
}

void
freerange(void *vstart, void *vend)
{
  char *p;
  p = (char*)PGROUNDUP((uintptr_t)vstart);
  for(; p + PGSIZE <= (char*)vend; p += PGSIZE)
    kfree(p);
}
//PAGEBREAK: 21
// Free the page of physical memory pointed at by v,
// which normally should have been returned by a
// call to kalloc().  (The exception is when
// initializing the allocator; see kinit above.)
void
kfree(char *v)
{
  struct run *r;

  if((uintptr_t)v % PGSIZE || v < end || V2P(v) >= PHYSTOP)
    panic("kfree");

  // Fill with junk to catch dangling refs.
  memset(v, 1, PGSIZE);

  int node = node_of(V2P(v));
  if(kmem.use_lock)
    acquire(&kmem.lock[node]);
  r = (struct run*)v;
  r->next = kmem.freelist[node];
  kmem.freelist[node] = r;
  if(kmem.use_lock)
    release(&kmem.lock[node]);
}

// Allocate one 4096-byte page of physical memory.
// Returns a pointer that the kernel can use.
// Returns 0 if the memory cannot be allocated.
char*
kalloc(void)
{
  struct run *r = 0;
  int start = 0;
  struct proc *p = myproc();
  if(p)
    start = p->preferred_node % NNODES;
  for(int i=0;i<NNODES;i++){
    int node = (start + i) % NNODES;
    if(kmem.use_lock)
      acquire(&kmem.lock[node]);
    r = kmem.freelist[node];
    if(r){
      kmem.freelist[node] = r->next;
      if(kmem.use_lock)
        release(&kmem.lock[node]);
      break;
    }
    if(kmem.use_lock)
      release(&kmem.lock[node]);
  }
  return (char*)r;
}

