# Analysis Report: `read_file` for `kernel/mmu64.c`

## Tool Call:
```
default_api.read_file(absolute_path = "/Users/eirikr/Documents/GitHub/exov6/kernel/mmu64.c")
```

## Output:
```c
#ifdef __x86_64__
#include "param.h"
#include "types.h"
#include "defs.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include <string.h>

extern char data[];

static pte_t *
walkpml4(pml4e_t *pml4, const void *va, int alloc)
{
  pml4e_t *pml4e;
  pdpe_t *pdp;
  pdpe_t *pdpe;
  pde_t *pd;
  pte_t *pt;

  pml4e = &pml4[PML4(va)];
  if(*pml4e & PTE_P){
    pdp = (pdpe_t*)P2V(PTE_ADDR(*pml4e));
  } else {
    if(!alloc || (pdp = (pdpe_t*)kalloc()) == 0)
      return 0;
    memset(pdp, 0, PGSIZE);
    *pml4e = V2P(pdp) | PTE_P | PTE_W | PTE_U;
  }

  pdpe = &pdp[PDPX(va)];
  if(*pdpe & PTE_P){
    pd = (pde_t*)P2V(PTE_ADDR(*pdpe));
  } else {
    if(!alloc || (pd = (pde_t*)kalloc()) == 0)
      return 0;
    memset(pd, 0, PGSIZE);
    *pdpe = V2P(pd) | PTE_P | PTE_W | PTE_U;
  }

  pde_t *pde = &pd[PDX(va)];
  if(*pde & PTE_P){
    pt = (pte_t*)P2V(PTE_ADDR(*pde));
  } else {
    if(!alloc || (pt = (pte_t*)kalloc()) == 0)
      return 0;
    memset(pt, 0, PGSIZE);
    *pde = V2P(pt) | PTE_P | PTE_W | PTE_U;
  }

  return &pt[PTX(va)];
}

static int
mappages64(pml4e_t *pml4, void *va, uint32_t size, uint64_t pa, int perm)
{
  char *a, *last;
  pte_t *pte;

  a = (char*)PGROUNDDOWN((uintptr_t)va);
  last = (char*)PGROUNDDOWN(((uintptr_t)va) + size - 1);
  for(;;){
    if((pte = walkpml4(pml4, a, 1)) == 0)
      return -1;
    if(*pte & PTE_P)
      panic("remap");
    *pte = pa | perm | PTE_P;
    if(a == last)
      break;
    a += PGSIZE;
    pa += PGSIZE;
  }
  return 0;
}

pml4e_t*
setupkvm64(void)
{
  pml4e_t *pml4;
  struct kmap { void *virt; uint32_t phys_start; uint32_t phys_end; int perm; };
  static struct kmap kmap[] = {
    { (void*)KERNBASE, 0,             EXTMEM,    PTE_W},
    { (void*)KERNLINK, V2P(KERNLINK), V2P(data), 0},
    { (void*)data,     V2P(data),     PHYSTOP,   PTE_W},
    { (void*)DEVSPACE, DEVSPACE,      0,         PTE_W},
  };
  struct kmap *k;

  if((pml4 = (pml4e_t*)kalloc()) == 0)
    return 0;
  memset(pml4, 0, PGSIZE);
  if (P2V(PHYSTOP) > (void*)DEVSPACE)
    panic("PHYSTOP too high");
  for(k = kmap; k < &kmap[NELEM(kmap)]; k++)
    if(mappages64(pml4, k->virt, k->phys_end - k->phys_start,
                  (uint64_t)k->phys_start, k->perm) < 0) {
      kfree((char*)pml4);
      return 0;
    }
  return pml4;
}
#endif
```