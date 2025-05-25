#include "ddekit.h"
#include "procwrap.h"
#include "capwrap.h"
#include "user.h"

void ddekit_init(void) {}

int ddekit_process_spawn(struct ddekit_process *p, const char *path,
                         char *const argv[]) {
    return proc_spawn((proc_handle_t *)p, path, argv);
}

int ddekit_process_wait(struct ddekit_process *p) {
    return proc_wait((proc_handle_t *)p);
}

void ddekit_process_exit(int code) { proc_exit(code); }

void ddekit_yield(void) { yield(); }

exo_cap ddekit_cap_alloc_page(void) { return capwrap_alloc_page(); }

enum exo_ipc_status ddekit_cap_send(exo_cap dest, const void *buf, size_t len) {
    return capwrap_send(dest, buf, len);
}

enum exo_ipc_status ddekit_cap_recv(exo_cap src, void *buf, size_t len) {
    return capwrap_recv(src, buf, len);
}
