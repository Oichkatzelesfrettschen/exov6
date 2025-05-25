#include "microkernel/microkernel.h"

exo_cap mk_cap_alloc_page(void) {
    return cap_alloc_page();
}

int mk_cap_free_page(exo_cap cap) {
    return cap_unbind_page(cap);
}

int mk_obtain_cap(exo_cap cap, exo_cap *out) {
    if (!out)
        return -1;
    if (cap_inc(cap.id) < 0)
        return -1;
    *out = cap;
    return 0;
}

int mk_revoke_cap(exo_cap cap) {
    return cap_revoke(cap.id);
}
