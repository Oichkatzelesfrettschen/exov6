/**
 * @file driver.c
 * @brief Driver spawn and connection support for LibOS
 *
 * Provides user-space implementation of driver_spawn and driver_connect
 * which use the underlying exokernel primitives.
 */

#include "types.h"
#include "user.h"
#include "exo.h"
#include "ipc.h"

/* Forward declare POSIX execv wrapper */
extern int execv(const char *path, char *const argv[]);

/**
 * Spawn a new driver process
 *
 * @param path Path to the driver executable
 * @param argv Argument vector (NULL-terminated)
 * @return PID of the spawned process on success, -1 on failure
 */
int driver_spawn(const char *path, char *const argv[]) {
    if (!path || !argv)
        return -1;

    int pid = fork();
    if (pid < 0)
        return -1;

    if (pid == 0) {
        /* Child: replace process image with driver */
        execv(path, argv);
        /* execv only returns on failure */
        exit(1);
    }

    /* Parent: return child PID */
    return pid;
}

/**
 * Connect to a driver process via endpoint capability
 *
 * @param pid Target driver PID
 * @param ep Endpoint capability for communication
 * @return 0 on success, -1 on failure
 */
int driver_connect(int pid, exo_cap ep) {
    if (pid <= 0)
        return -1;

    /* Send connection request to the driver's endpoint */
    zipc_msg_t msg = {0};
    msg.w0 = 0;  /* Connection request type */
    msg.w1 = (uint32_t)pid;
    msg.w2 = ep.id;
    msg.w3 = ep.owner;

    return exo_send(ep, &msg, sizeof(msg));
}
