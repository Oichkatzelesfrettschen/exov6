/**
 * @file service.c
 * @brief ExoV6 Service Registry Client (Phase 12.1)
 *
 * ╔═══════════════════════════════════════════════════════════════════════════╗
 * ║  LIONS' COMMENTARY FOR THE POST-MONOLITHIC AGE                            ║
 * ║                                                                           ║
 * ║  LESSON: Service discovery is a user-space protocol, not kernel magic.   ║
 * ║                                                                           ║
 * ║  In traditional UNIX, "well-known" services are found via:               ║
 * ║    - /etc/services (port numbers)                                        ║
 * ║    - /var/run/*.pid (PID files)                                          ║
 * ║    - Hardcoded paths (/dev/log, /tmp/.X11-unix)                          ║
 * ║                                                                           ║
 * ║  In ExoV6, the init process (PID 1) maintains a simple registry:         ║
 * ║    - Services register their name and PID                                ║
 * ║    - Clients look up services by name                                    ║
 * ║    - All communication via IPC messages                                  ║
 * ║                                                                           ║
 * ║  This is similar to:                                                      ║
 * ║    - Mach's bootstrap server                                             ║
 * ║    - seL4's naming server                                                ║
 * ║    - Plan 9's factotum                                                   ║
 * ╚═══════════════════════════════════════════════════════════════════════════╝
 */

#include <stdint.h>
#include <types.h>
#include <service.h>

/* ═══════════════════════════════════════════════════════════════════════════
 * External Dependencies
 * ═══════════════════════════════════════════════════════════════════════════ */

/* IPC */
extern int sys_ipc_send(int target_pid, uint64 w0, uint64 w1, uint64 w2);
extern int sys_ipc_recv(int *sender_pid, uint64 *w0, uint64 *w1, uint64 *w2);

/* Debug */
extern void print(const char *s);

/* ═══════════════════════════════════════════════════════════════════════════
 * Helper: Pack service name into uint64s
 *
 * Names are max 16 chars, packed into two 64-bit words for IPC.
 * ═══════════════════════════════════════════════════════════════════════════ */

static void pack_name(const char *name, uint64 *w1, uint64 *w2) {
    *w1 = 0;
    *w2 = 0;

    /* Pack up to 8 chars into w1 */
    for (int i = 0; i < 8 && name[i]; i++) {
        *w1 |= ((uint64)(unsigned char)name[i]) << (i * 8);
    }

    /* Pack next 8 chars into w2 */
    int len1 = 0;
    while (len1 < 8 && name[len1]) len1++;

    for (int i = 0; i < 8 && name[len1 + i]; i++) {
        *w2 |= ((uint64)(unsigned char)name[len1 + i]) << (i * 8);
    }
}

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
 * service_register() - Register as a Named Service
 *
 * Sends: SVC_REQ_REGISTER, name (packed)
 * Receives: SVC_OK or error code
 * ═══════════════════════════════════════════════════════════════════════════ */

int service_register(const char *name) {
    uint64 w1, w2;
    pack_name(name, &w1, &w2);

    /* Send register request to init */
    if (sys_ipc_send(INIT_PID, SVC_REQ_REGISTER, w1, w2) < 0) {
        return -1;
    }

    /* Wait for response */
    int sender;
    uint64 r0, r1, r2;
    if (sys_ipc_recv(&sender, &r0, &r1, &r2) < 0) {
        return -1;
    }

    /* Verify sender */
    if (sender != INIT_PID) {
        return -1;
    }

    return (int)r0;  /* Result code */
}

/* ═══════════════════════════════════════════════════════════════════════════
 * service_lookup() - Look Up a Service by Name
 *
 * Sends: SVC_REQ_LOOKUP, name (packed)
 * Receives: SVC_OK + PID, or error code
 * ═══════════════════════════════════════════════════════════════════════════ */

int service_lookup(const char *name) {
    uint64 w1, w2;
    pack_name(name, &w1, &w2);

    /* Send lookup request to init */
    if (sys_ipc_send(INIT_PID, SVC_REQ_LOOKUP, w1, w2) < 0) {
        return -1;
    }

    /* Wait for response */
    int sender;
    uint64 r0, r1, r2;
    if (sys_ipc_recv(&sender, &r0, &r1, &r2) < 0) {
        return -1;
    }

    /* Verify sender */
    if (sender != INIT_PID) {
        return -1;
    }

    /* r0 = result, r1 = PID if found */
    if ((int)r0 == SVC_OK) {
        return (int)r1;  /* Service PID */
    }

    return (int)r0;  /* Error code */
}

/* ═══════════════════════════════════════════════════════════════════════════
 * service_unregister() - Unregister a Service
 * ═══════════════════════════════════════════════════════════════════════════ */

int service_unregister(const char *name) {
    uint64 w1, w2;
    pack_name(name, &w1, &w2);

    /* Send unregister request to init */
    if (sys_ipc_send(INIT_PID, SVC_REQ_UNREGISTER, w1, w2) < 0) {
        return -1;
    }

    /* Wait for response */
    int sender;
    uint64 r0, r1, r2;
    if (sys_ipc_recv(&sender, &r0, &r1, &r2) < 0) {
        return -1;
    }

    if (sender != INIT_PID) {
        return -1;
    }

    return (int)r0;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * PEDAGOGICAL NOTE
 *
 * This client library shows how microkernel/exokernel services work:
 *
 * 1. NO KERNEL INVOLVEMENT: The kernel doesn't know about "services".
 *    It just delivers IPC messages between processes.
 *
 * 2. NAMING IS POLICY: Service names are arbitrary strings chosen by
 *    convention. "fs", "net", "console" are just conventions.
 *
 * 3. INIT IS SPECIAL: PID 1 is the only well-known endpoint.
 *    Everything else is discovered dynamically.
 *
 * Compare to macOS/XNU:
 *   - bootstrap_register() / bootstrap_look_up()
 *   - launchd is the modern equivalent
 *
 * Compare to seL4:
 *   - Capability to naming server passed at process creation
 *   - All service discovery via naming server
 * ═══════════════════════════════════════════════════════════════════════════ */
