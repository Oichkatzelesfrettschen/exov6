/**
 * @file service.h
 * @brief ExoV6 Service Registry API (Phase 12.1)
 *
 * Service discovery for the exokernel multi-application society.
 * Services register with init (PID 1), clients look up by name.
 *
 * Example:
 *   // In fs_srv:
 *   service_register("fs");
 *
 *   // In client:
 *   int fs_pid = service_lookup("fs");
 *   sys_ipc_send(fs_pid, FS_REQ_OPEN, ...);
 */

#ifndef SERVICE_H
#define SERVICE_H

#include <stdint.h>

/* ═══════════════════════════════════════════════════════════════════════════
 * Well-Known PIDs
 * ═══════════════════════════════════════════════════════════════════════════ */

#define INIT_PID        1   /* Init process - service registry */
#define FS_SERVER_PID   2   /* File server (legacy, for compatibility) */

/* ═══════════════════════════════════════════════════════════════════════════
 * Service Registry Protocol
 *
 * All messages go to init (PID 1)
 * ═══════════════════════════════════════════════════════════════════════════ */

#define SVC_REQ_REGISTER    0x100   /* Register a service */
#define SVC_REQ_LOOKUP      0x101   /* Look up a service */
#define SVC_REQ_UNREGISTER  0x102   /* Unregister a service */
#define SVC_REQ_LIST        0x103   /* List all services */

/* Response codes */
#define SVC_OK              0       /* Success */
#define SVC_ERR_NOTFOUND    -1      /* Service not found */
#define SVC_ERR_EXISTS      -2      /* Service already registered */
#define SVC_ERR_FULL        -3      /* Registry full */
#define SVC_ERR_INVALID     -4      /* Invalid request */

/* ═══════════════════════════════════════════════════════════════════════════
 * Service Registry API
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * Register this process as a named service
 * @param name Service name (max 15 chars)
 * @return 0 on success, negative on error
 */
int service_register(const char *name);

/**
 * Look up a service by name
 * @param name Service name
 * @return Service PID (>= 1) or negative on error
 */
int service_lookup(const char *name);

/**
 * Unregister this process's service
 * @param name Service name
 * @return 0 on success, negative on error
 */
int service_unregister(const char *name);

/**
 * Get own process ID
 * @return Process ID
 */
int getpid(void);

#endif /* SERVICE_H */
