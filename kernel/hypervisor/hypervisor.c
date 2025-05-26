#include "types.h"
#include "defs.h"
#include "cap.h"
#include "proc.h"
#include "hypervisor.h"
#include <string.h>

// Allocate a capability referencing the hypervisor control interface.
exo_cap exo_alloc_hypervisor(void) {
    int id = cap_table_alloc(CAP_TYPE_HYPERVISOR, 0, EXO_RIGHT_CTL, myproc()->pid);
    return cap_new(id >= 0 ? id : 0, EXO_RIGHT_CTL, myproc()->pid);
}

// Minimal stub that pretends to launch a guest kernel image.
int hv_launch_guest(exo_cap cap, const char *path) {
    struct cap_entry e;
    if (cap_table_lookup(cap.id, &e) < 0 || e.type != CAP_TYPE_HYPERVISOR)
        return -1;
    cprintf("hypervisor: launching guest %s\n", path);
    // No actual virtualization yet.
    return 0;
}
