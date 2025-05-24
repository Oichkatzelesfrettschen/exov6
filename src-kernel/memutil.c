#include "types.h"
#include "memlayout.h"
#include "mmu.h"

// Lookup a page table entry without allocating pages.
pte_t *pte_lookup(pde_t *pgdir, const void *va) {
#ifdef __x86_64__
  pml4e_t *pml4e = &((pml4e_t *)pgdir)[PML4(va)];
  if (!(*pml4e & PTE_P))
    return 0;
  pdpe_t *pdp = (pdpe_t *)P2V(PTE_ADDR(*pml4e));
  pdpe_t *pdpe = &pdp[PDPX(va)];
  if (!(*pdpe & PTE_P))
    return 0;
  pde_t *pd = (pde_t *)P2V(PTE_ADDR(*pdpe));
  pde_t *pde = &pd[PDX(va)];
  if (!(*pde & PTE_P))
    return 0;
  pte_t *pt = (pte_t *)P2V(PTE_ADDR(*pde));
  return &pt[PTX(va)];
#else
  pde_t *pde = &pgdir[PDX(va)];
  if (!(*pde & PTE_P))
    return 0;
  pte_t *pt = (pte_t *)P2V(PTE_ADDR(*pde));
  return &pt[PTX(va)];
#endif
}

// Invalidate a single TLB entry corresponding to va.
void tlb_flush_page(void *va) {
#ifdef __x86_64__
  asm volatile("invlpg (%0)" : : "r"(va) : "memory");
#else
  asm volatile("invlpg (%0)" : : "r"(va) : "memory");
#endif
}

// Atomic compare-and-swap for pointers.
void *atomic_cas_ptr(volatile void **target, void *cmp, void *newval) {
  void *expected = cmp;
  __atomic_compare_exchange_n(target, &expected, newval, 0, __ATOMIC_SEQ_CST,
                              __ATOMIC_SEQ_CST);
  return expected;
}
