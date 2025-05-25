#include "ddekit.h"
#include "user.h"

int main(void) {
    ddekit_init();
    char *argv[] = { "hello_channel", 0 };
    struct ddekit_process child;
    ddekit_process_spawn(&child, "hello_channel", argv);
    ddekit_process_wait(&child);

    char buf[] = "demo";
    exo_cap page = ddekit_cap_alloc_page();
    ddekit_cap_send(page, buf, sizeof(buf));
    printf(1, "ddekit port demo complete\n");
    exit();
}
