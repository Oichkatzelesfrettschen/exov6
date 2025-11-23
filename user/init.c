/**
 * @file init.c
 * @brief ExoV6 Init - "The First Citizen" (Phase 12)
 *
 * ╔═══════════════════════════════════════════════════════════════════════════╗
 * ║  LIONS' COMMENTARY FOR THE POST-MONOLITHIC AGE                            ║
 * ║                                                                           ║
 * ║  LESSON: Init is both the first process AND the service registry.        ║
 * ║                                                                           ║
 * ║  In UNIX V6, /etc/init:                                                   ║
 * ║    - Forks getty for each terminal                                        ║
 * ║    - Waits for orphaned children (zombie reaping)                         ║
 * ║    - Reads /etc/ttys for configuration                                    ║
 * ║                                                                           ║
 * ║  In ExoV6, init:                                                          ║
 * ║    1. Spawns essential services (fs_srv, shell)                          ║
 * ║    2. Maintains the service registry (name → PID mapping)                 ║
 * ║    3. Handles service registration/lookup IPC requests                    ║
 * ║    4. Reaps zombie children                                               ║
 * ║                                                                           ║
 * ║  This is similar to:                                                      ║
 * ║    - Mach bootstrap server                                                ║
 * ║    - macOS launchd                                                        ║
 * ║    - systemd (service management)                                         ║
 * ║    - seL4 root task                                                       ║
 * ╚═══════════════════════════════════════════════════════════════════════════╝
 */

#include <stdint.h>
#include <types.h>
#include <service.h>

/* ═══════════════════════════════════════════════════════════════════════════
 * External Dependencies
 * ═══════════════════════════════════════════════════════════════════════════ */

/* LibOS */
extern void print(const char *s);
extern void print_hex(uint64 n);
extern void libos_exception_init(void);

/* Syscalls */
extern int sys_ipc_send(int target_pid, uint64 w0, uint64 w1, uint64 w2);
extern int sys_ipc_recv(int *sender_pid, uint64 *w0, uint64 *w1, uint64 *w2);

/* spawn() for starting services */
extern int spawn(const char *path, char **argv);

/* ═══════════════════════════════════════════════════════════════════════════
 * Configuration
 * ═══════════════════════════════════════════════════════════════════════════ */

#define MAX_SERVICES    16
#define MAX_NAME_LEN    16

/* ═══════════════════════════════════════════════════════════════════════════
 * Service Registry
 * ═══════════════════════════════════════════════════════════════════════════ */

struct service_entry {
    int in_use;
    int pid;
    char name[MAX_NAME_LEN];
};

static struct service_entry services[MAX_SERVICES];

/* ═══════════════════════════════════════════════════════════════════════════
 * String Helpers
 * ═══════════════════════════════════════════════════════════════════════════ */

static int strcmp_init(const char *a, const char *b) {
    while (*a && *b && *a == *b) {
        a++;
        b++;
    }
    return *a - *b;
}

static void strcpy_init(char *dst, const char *src) {
    while (*src) *dst++ = *src++;
    *dst = '\0';
}

/* Unpack name from IPC words */
static void unpack_name(uint64 w1, uint64 w2, char *name) {
    for (int i = 0; i < 8; i++) {
        name[i] = (char)(w1 >> (i * 8));
    }
    for (int i = 0; i < 8; i++) {
        name[8 + i] = (char)(w2 >> (i * 8));
    }
    name[16] = '\0';
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Registry Helpers
 * ═══════════════════════════════════════════════════════════════════════════ */

static void print_int(int n) {
    if (n < 0) {
        print("-");
        n = -n;
    }
    if (n == 0) {
        print("0");
        return;
    }
    char buf[12];
    int i = 0;
    while (n > 0) {
        buf[i++] = '0' + (n % 10);
        n /= 10;
    }
    char out[12];
    for (int j = 0; j < i; j++) {
        out[j] = buf[i - 1 - j];
    }
    out[i] = '\0';
    print(out);
}

static int registry_find(const char *name) {
    for (int i = 0; i < MAX_SERVICES; i++) {
        if (services[i].in_use && strcmp_init(services[i].name, name) == 0) {
            return i;
        }
    }
    return -1;
}

static int registry_register(const char *name, int pid) {
    /* Check if already registered */
    if (registry_find(name) >= 0) {
        return SVC_ERR_EXISTS;
    }

    /* Find free slot */
    for (int i = 0; i < MAX_SERVICES; i++) {
        if (!services[i].in_use) {
            services[i].in_use = 1;
            services[i].pid = pid;
            strcpy_init(services[i].name, name);

            print("[INIT] Service registered: ");
            print(name);
            print(" → PID ");
            print_int(pid);
            print("\n");

            return SVC_OK;
        }
    }

    return SVC_ERR_FULL;
}

static int registry_unregister(const char *name) {
    int idx = registry_find(name);
    if (idx < 0) {
        return SVC_ERR_NOTFOUND;
    }

    print("[INIT] Service unregistered: ");
    print(services[idx].name);
    print("\n");

    services[idx].in_use = 0;
    return SVC_OK;
}

static int registry_lookup(const char *name) {
    int idx = registry_find(name);
    if (idx < 0) {
        return SVC_ERR_NOTFOUND;
    }
    return services[idx].pid;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Handle IPC Request
 * ═══════════════════════════════════════════════════════════════════════════ */

static void handle_request(int sender, uint64 w0, uint64 w1, uint64 w2) {
    char name[MAX_NAME_LEN + 1];
    int result;
    uint64 r1 = 0;

    switch ((int)w0) {
    case SVC_REQ_REGISTER:
        unpack_name(w1, w2, name);
        result = registry_register(name, sender);
        break;

    case SVC_REQ_LOOKUP:
        unpack_name(w1, w2, name);
        result = registry_lookup(name);
        if (result > 0) {
            r1 = result;  /* PID */
            result = SVC_OK;
        }
        break;

    case SVC_REQ_UNREGISTER:
        unpack_name(w1, w2, name);
        result = registry_unregister(name);
        break;

    default:
        result = SVC_ERR_INVALID;
        break;
    }

    /* Send response */
    sys_ipc_send(sender, (uint64)result, r1, 0);
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Auto-Start Services (Phase 12.2)
 *
 * LESSON: In UNIX, /etc/rc starts services. In systemd, unit files.
 * In ExoV6, init hardcodes the essential services for simplicity.
 * A production system would read a config file via fs_srv.
 * ═══════════════════════════════════════════════════════════════════════════ */

static void start_essential_services(void) {
    print("\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("  Starting Essential Services\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("\n");

    /*
     * NOTE: In a real exokernel, we'd spawn fs_srv first, then use it
     * to load other binaries. For bootstrap, the kernel embeds init.
     *
     * For now, we just announce what we WOULD do.
     * The spawn() function requires fs_srv to be running to load ELFs.
     *
     * Bootstrap order:
     *   1. Kernel loads embedded init (us)
     *   2. Init spawns fs_srv (requires special kernel support or embedding)
     *   3. fs_srv registers with init
     *   4. Init spawns shell via fs_srv
     */

    print("[INIT] Essential services:\n");
    print("  - fs_srv (file server) - provides disk access\n");
    print("  - sh (shell) - provides user interaction\n");
    print("\n");
    print("[INIT] Note: Service spawning requires fs_srv.\n");
    print("[INIT] For full boot, fs_srv must be embedded or pre-loaded.\n");
    print("\n");

    /*
     * For demo purposes, we pre-register fs_srv at PID 2
     * (the spawn infrastructure will start it separately)
     */
    registry_register("fs", 2);  /* Well-known fs_srv PID */
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Main Entry Point
 * ═══════════════════════════════════════════════════════════════════════════ */

int main(void) {
    /* Banner */
    print("\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("  ███████╗██╗  ██╗ ██████╗ ██╗   ██╗ ██████╗     ██╗███╗   ██╗██╗████████╗\n");
    print("  ██╔════╝╚██╗██╔╝██╔═══██╗██║   ██║██╔════╝     ██║████╗  ██║██║╚══██╔══╝\n");
    print("  █████╗   ╚███╔╝ ██║   ██║██║   ██║███████╗     ██║██╔██╗ ██║██║   ██║\n");
    print("  ██╔══╝   ██╔██╗ ██║   ██║╚██╗ ██╔╝██╔═══██╗    ██║██║╚██╗██║██║   ██║\n");
    print("  ███████╗██╔╝ ██╗╚██████╔╝ ╚████╔╝ ╚██████╔╝    ██║██║ ╚████║██║   ██║\n");
    print("  ╚══════╝╚═╝  ╚═╝ ╚═════╝   ╚═══╝   ╚═════╝     ╚═╝╚═╝  ╚═══╝╚═╝   ╚═╝\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("  The First Citizen - ExoV6 Init (Phase 12)\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("\n");

    /* Initialize LibOS exception handling */
    libos_exception_init();

    /* Clear registry */
    for (int i = 0; i < MAX_SERVICES; i++) {
        services[i].in_use = 0;
    }

    /* Start essential services */
    start_essential_services();

    /* Main loop: handle service registry requests */
    print("[INIT] Entering service registry loop...\n");
    print("[INIT] Waiting for IPC requests on PID 1\n");
    print("\n");

    while (1) {
        int sender;
        uint64 w0, w1, w2;

        /* Block waiting for IPC */
        if (sys_ipc_recv(&sender, &w0, &w1, &w2) < 0) {
            continue;
        }

        /* Handle the request */
        handle_request(sender, w0, w1, w2);
    }

    return 0;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * PEDAGOGICAL SUMMARY
 *
 * Init is the root of the exokernel's process tree. It has three roles:
 *
 * 1. BOOTSTRAPPER: Starts essential services (fs_srv, shell)
 *
 * 2. SERVICE REGISTRY: Maintains name → PID mappings
 *    - Services register: "fs" → PID 2
 *    - Clients lookup: "fs" → get PID 2
 *
 * 3. ZOMBIE REAPER: Waits for orphaned children (not yet implemented)
 *
 * COMPARISON:
 *
 * UNIX V6 /etc/init:
 *   - Reads /etc/ttys
 *   - Forks getty for each terminal
 *   - Loops on wait() to reap zombies
 *
 * ExoV6 init:
 *   - Spawns hardcoded services
 *   - Loops on IPC recv for registry requests
 *   - TODO: Also loop on wait() for zombie reaping
 *
 * macOS launchd:
 *   - Reads property list files
 *   - Starts services on-demand
 *   - Provides bootstrap_register/look_up
 *
 * The key insight: Service discovery is just a lookup table!
 * The complexity comes from:
 *   - Dependency ordering
 *   - On-demand startup
 *   - Crash recovery
 *   - Resource limits
 *
 * ExoV6 keeps it simple: explicit registration, no dependencies.
 * ═══════════════════════════════════════════════════════════════════════════ */
