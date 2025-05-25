#include "microkernel/microkernel.h"

exo_cap mk_cap_alloc_page(void) {
    return cap_alloc_page();
}

int mk_cap_free_page(exo_cap cap) {
    return cap_unbind_page(cap);
}
