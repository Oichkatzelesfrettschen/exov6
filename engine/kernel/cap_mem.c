#include "exo_mem.h"
#include "defs.h"
#include "cap.h"
#include "memlayout.h"

void *cap_kalloc(exo_cap *out)
{
    *out = exo_alloc_page();
    if(out->id == 0)
        return 0;
    struct cap_entry e;
    if(cap_table_lookup(out->id, &e) < 0)
        return 0;
    return P2V(e.resource);
}

void cap_kfree(exo_cap cap)
{
    exo_unbind_page(cap);
}
