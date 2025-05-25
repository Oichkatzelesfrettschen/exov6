#pragma once
#include <stddef.h>
#include <stdint.h>
#define IOMMU_PTE_P 0x1

typedef uint64_t iommu_pte_t;

struct iommu_dom {
  iommu_pte_t *pt;
  size_t npages;
};

#define IOMMU_OP_MAP 0xA0
#define IOMMU_OP_UNMAP 0xA1
#define IOMMU_OP_REVOKE 0xA2

int iommu_map(struct iommu_dom *dom, uintptr_t iova, uintptr_t pa, size_t len,
              int perm);
int iommu_unmap(struct iommu_dom *dom, uintptr_t iova, size_t len);
void iommu_sync(struct iommu_dom *dom);
void iommu_revoke(struct iommu_dom *dom);

#ifdef __cplusplus
extern "C" {
#endif

int iommu_map_call(uintptr_t iova, uintptr_t pa, size_t len);
int iommu_unmap_call(uintptr_t iova, size_t len);
int iommu_revoke_call(void);

#ifdef __cplusplus
}
#endif
