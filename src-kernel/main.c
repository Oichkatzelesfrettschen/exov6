#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "dag.h"
#include "cap.h"
#include "x86.h"
#include "exo_stream.h"
#include "exo_ipc.h"

static void startothers(void);
static void mpmain(void) __attribute__((noreturn));
#ifdef __x86_64__
extern pml4e_t *kpgdir;
#else
extern pde_t *kpgdir;
#endif
extern char end[]; // first address after kernel loaded from ELF file

// Bootstrap processor starts running C code here.
// Allocate a real stack and switch to it, first
// doing some setup required for memory allocator to work.
int main(void) {
  kinit1(end, P2V(4 * 1024 * 1024)); // phys page allocator
  kvmalloc();                        // kernel page table
  mpinit();                          // detect other processors
  lapicinit();                       // interrupt controller
  seginit();                         // segment descriptors
  picinit();                         // disable pic
  ioapicinit();                      // another interrupt controller
  consoleinit();                     // console hardware
  uartinit();                        // serial port
  cap_table_init();                  // initialize capability table
  rcuinit();                         // rcu subsystem
  pinit();                           // process table
  tvinit();                          // trap vectors
  binit();                           // buffer cache
  fileinit();                        // file table
  ideinit();                         // disk
  dag_sched_init();                  // initialize DAG scheduler
  beatty_sched_init();               // initialize Beatty scheduler
  startothers();                              // start other processors
  kinit2(P2V(4 * 1024 * 1024), P2V(PHYSTOP)); // must come after startothers()
  userinit();                                 // first user process
  mpmain();                                   // finish this processor's setup
}

// Other CPUs jump here from entryother.S.
static void mpenter(void) {
  switchkvm();
  seginit();
  lapicinit();
  mpmain();
}

// Common CPU setup code.
static void mpmain(void) {
  cprintf("cpu%d: starting %d\n", cpuid(), cpuid());
  idtinit();                    // load idt register
  xchg(&(mycpu()->started), 1); // tell startothers() we're up
  scheduler();                  // start running processes
}

#ifdef __x86_64__
// 64-bit boot code does not use a statically allocated entry page table.
#else
pde_t entrypgdir[]; // For entry.S
#endif

// Start the non-boot (AP) processors.
static void startothers(void) {
#ifdef __x86_64__
  extern uint8_t _binary_entryother64_start[], _binary_entryother64_size[];
#else
  extern uint8_t _binary_entryother_start[], _binary_entryother_size[];
#endif
  uint8_t *code;
  struct cpu *c;
  char *stack;

  // Write entry code to unused memory at 0x7000.
  // The linker has placed the image of entryother.S in
  // _binary_entryother_start.
  code = P2V(0x7000);
#ifdef __x86_64__

  memmove(code, _binary_entryother64_start, (size_t)_binary_entryother64_size);

#else
  memmove(code, _binary_entryother_start, (uint32_t)_binary_entryother_size);
#endif

  for (c = cpus; c < cpus + ncpu; c++) {
    if (c == mycpu()) // We've started already.
      continue;

    // Tell entryother.S what stack to use, where to enter, and what
    // pgdir to use. We cannot use kpgdir yet, because the AP processor
    // is running in low  memory, so we use entrypgdir for the APs too.
    stack = kalloc();
    if (stack == 0)
      panic("startothers: out of memory");
#ifdef __x86_64__
    *(uint64_t *)(code - 8) = (uint64_t)stack + KSTACKSIZE;
    *(void (**)(void))(code - 16) = mpenter;
#else
    *(void **)(code - 4) = stack + KSTACKSIZE;
    *(void (**)(void))(code - 8) = mpenter;
    *(int **)(code - 12) = (void *)V2P(entrypgdir);
#endif

    lapicstartap(c->apicid, V2P(code));

    // wait for cpu to finish mpmain()
    while (c->started == 0)
      ;
  }
}

// The boot page table used in entry.S and entryother.S.
// Page directories (and page tables) must start on page boundaries,
// hence the __aligned__ attribute.
// PTE_PS in a page directory entry enables 4Mbyte pages.

#ifndef __x86_64__
__attribute__((__aligned__(PGSIZE))) pde_t entrypgdir[NPDENTRIES] = {
    // Map VA's [0, 4MB) to PA's [0, 4MB)
    [0] = (0) | PTE_P | PTE_W | PTE_PS,
    // Map VA's [KERNBASE, KERNBASE+4MB) to PA's [0, 4MB)
    [KERNBASE >> PDXSHIFT] = (0) | PTE_P | PTE_W | PTE_PS,
};
#endif

// PAGEBREAK!
//  Blank page.
// PAGEBREAK!
//  Blank page.
// PAGEBREAK!
//  Blank page.
