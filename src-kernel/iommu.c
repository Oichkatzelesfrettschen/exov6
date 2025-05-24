#include "iommu.h"
#include "defs.h"
#include "mmu.h"
#include <stdint.h>
#include <string.h>

int
iommu_map(struct iommu_dom *dom, uintptr_t iova, uintptr_t pa,
          size_t len, int perm)
{
    if(!dom || !dom->pt || (iova % PGSIZE) || (pa % PGSIZE) ||
       (len % PGSIZE))
        return -1;
    size_t pages = len / PGSIZE;
    for(size_t i = 0; i < pages; i++){
        size_t idx = (iova / PGSIZE) + i;
        if(idx >= dom->npages)
            return -1;
        if(dom->pt[idx] & IOMMU_PTE_P)
            return -1;
        dom->pt[idx] = (pa + i*PGSIZE) | perm | IOMMU_PTE_P;
    }
    iommu_sync(dom);
    return 0;
}

int
iommu_unmap(struct iommu_dom *dom, uintptr_t iova, size_t len)
{
    if(!dom || !dom->pt || (iova % PGSIZE) || (len % PGSIZE))
        return -1;
    size_t pages = len / PGSIZE;
    for(size_t i = 0; i < pages; i++){
        size_t idx = (iova / PGSIZE) + i;
        if(idx >= dom->npages || !(dom->pt[idx] & IOMMU_PTE_P))
            return -1;
        dom->pt[idx] = 0;
    }
    iommu_sync(dom);
    return 0;
}

void
iommu_sync(struct iommu_dom *dom)
{
    (void)dom;
    // In hardware this would flush IOTLB; no-op in mock implementation.
}

void
iommu_revoke(struct iommu_dom *dom)
{
    if(!dom || !dom->pt)
        return;
    for(size_t i = 0; i < dom->npages; i++)
        dom->pt[i] = 0;
    iommu_sync(dom);
}
