#include "ddekit.h"
#include "driver.h"
#include "user.h"

void ddekit_init(void) {}

int ddekit_process_spawn(struct ddekit_process *p, const char *path,
                         char *const argv[]) {
    int pid = driver_spawn(path, argv);
    if (p)
        p->pid = pid;
    return pid;
}

int ddekit_process_wait(struct ddekit_process *p) {
    if (!p)
        return -1;
    int r;
    while ((r = wait()) >= 0) {
        if (r == p->pid)
            return 0;
    }
    return -1;
}

void ddekit_process_exit(int code) {
    (void)code;
    exit();
}

void ddekit_yield(void) { yield(); }

exo_cap ddekit_cap_alloc_page(void) { return cap_alloc_page(); }

int ddekit_cap_send(exo_cap dest, const void *buf, size_t len) {
    return cap_send(dest, buf, len);
}

int ddekit_cap_recv(exo_cap src, void *buf, size_t len) {
    return cap_recv(src, buf, len);
}
