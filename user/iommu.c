#include "iommu.h"
#include "ipc.h"

int
iommu_map_call(uintptr_t iova, uintptr_t pa, size_t len)
{
    zipc_msg_t m = {0};
    m.w0 = IOMMU_OP_MAP;
    m.w1 = iova;
    m.w2 = pa;
    m.w3 = len;
    zipc_call(&m);
    return (int)m.w0;
}

int
iommu_unmap_call(uintptr_t iova, size_t len)
{
    zipc_msg_t m = {0};
    m.w0 = IOMMU_OP_UNMAP;
    m.w1 = iova;
    m.w2 = len;
    zipc_call(&m);
    return (int)m.w0;
}

int
iommu_revoke_call(void)
{
    zipc_msg_t m = {0};
    m.w0 = IOMMU_OP_REVOKE;
    zipc_call(&m);
    return (int)m.w0;
}
