#include "ddekit.h"
#include "user.h"
#include <string.h>

int main(void) {
    ddekit_init();
    exo_cap fb = ddekit_cap_alloc_page();
    char buf[64];
    memset(buf, 0xff, sizeof(buf));
    ddekit_cap_send(fb, buf, sizeof(buf));
    printf(1, "fbdev demo complete\n");
    exit(0);
}
