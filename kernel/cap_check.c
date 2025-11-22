#include "cap_check.h"
#include "defs.h"
#include "proc.h"

int cap_check(exo_cap cap, uint32_t required_rights) {
    /* 1. Basic Validity Check */
    if (cap.id == EXO_CAP_INVALID) {
        return -1;
    }

    /* 2. Rights Check */
    if (!cap_has_rights(cap.rights, required_rights)) {
        return -1;
    }

    /* 3. Owner Check - Current process must own it */
    struct proc *p = myproc();
    if (p && cap.owner != p->pid) {
        return -1;
    }

    return 0;
}

int cap_check_type(exo_cap cap, uint32_t expected_type, uint32_t required_rights) {
    if (cap_check(cap, required_rights) < 0) {
        return -1;
    }

    /*
     * Check type stored in 'pa' field.
     * This assumes 'pa' holds the type for non-memory capabilities.
     * For memory capabilities, pa is an address, which is likely > 255.
     * So this check is valid if expected_type is a small enum value.
     */
    if (cap.pa != expected_type) {
        return -1;
    }

    return 0;
}

int cap_check_block(exo_blockcap cap, uint32_t required_rights) {
    /* 1. Basic Validity Check */
    /* Block caps don't have a distinct invalid ID, but rights=0 is useless */
    if (cap.rights == 0) {
        return -1;
    }

    /* 2. Rights Check */
    if (!cap_has_rights(cap.rights, required_rights)) {
        return -1;
    }

    /* 3. Owner Check */
    struct proc *p = myproc();
    if (p && cap.owner != p->pid) {
        return -1;
    }

    return 0;
}

int cap_check_owner(exo_cap cap, uint32_t pid) {
    if (cap.owner != pid) {
        return -1;
    }
    return 0;
}
