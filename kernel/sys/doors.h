/**
 * @file doors.h
 * @brief Illumos/Solaris-compatible Doors Interface
 *
 * Cleanroom implementation of doors for FeuerBird exokernel.
 * Uses the Wait Channel primitive for blocking/waking.
 *
 * Doors provide:
 * - Fast procedure-call IPC between processes
 * - File-descriptor based interface
 * - Zero-copy data transfer where possible
 * - Credential passing
 */
#pragma once

#include <stdint.h>

/* size_t for kernel context */
#ifndef _SIZE_T_DEFINED
#define _SIZE_T_DEFINED
typedef unsigned long size_t;
#endif

/**
 * Door descriptor information
 */
typedef uint64_t door_id_t;

/**
 * Door attributes (for door_getparam/door_setparam)
 */
#define DOOR_PARAM_DATA_MAX     1   /* Max data size */
#define DOOR_PARAM_DATA_MIN     2   /* Min data size */
#define DOOR_PARAM_DESC_MAX     3   /* Max descriptors */

/**
 * Door creation flags
 */
#define DOOR_UNREF          0x01    /* Deliver unref notification */
#define DOOR_UNREF_MULTI    0x40    /* Multiple unrefs allowed */
#define DOOR_PRIVATE        0x02    /* Private door (single thread) */
#define DOOR_REFUSE_DESC    0x04    /* Refuse descriptor passing */
#define DOOR_NO_CANCEL      0x08    /* Don't cancel on door_return */
#define DOOR_NO_DEPLETION_CB 0x10   /* No thread depletion callback */

/**
 * Door call flags
 */
#define DOOR_DESCRIPTOR     0x10    /* Pass descriptors */

/**
 * Door info flags (returned by door_info)
 */
#define DOOR_LOCAL          0x04    /* Door is local */
#define DOOR_REVOKED        0x08    /* Door has been revoked */
#define DOOR_IS_UNREF       0x10    /* Door has unref notification */

/**
 * Door descriptor passing
 */
typedef struct door_desc {
    uint32_t d_attributes;      /* Descriptor attributes */
    int d_data;                 /* Descriptor value */
} door_desc_t;

/**
 * Door argument structure
 */
typedef struct door_arg {
    char *data_ptr;             /* Argument data */
    size_t data_size;           /* Argument data size */
    door_desc_t *desc_ptr;      /* Descriptors to pass */
    uint32_t desc_num;          /* Number of descriptors */
    char *rbuf;                 /* Result buffer */
    size_t rsize;               /* Result buffer size */
} door_arg_t;

/**
 * Door info structure
 */
typedef struct door_info {
    int di_target;              /* Target process PID */
    door_id_t di_uniquifier;    /* Unique door ID */
    uint32_t di_attributes;     /* Door attributes */
    void *di_proc;              /* Server procedure (if local) */
    void *di_data;              /* Server cookie (if local) */
} door_info_t;

/**
 * Door server procedure type
 */
typedef void (*door_server_proc_t)(void *cookie, char *argp, size_t arg_size,
                                   door_desc_t *dp, uint32_t n_desc);

/**
 * Create a door
 *
 * @param proc      Server procedure to handle calls
 * @param cookie    Cookie passed to server procedure
 * @param attr      Door attributes
 * @return          Door fd on success, -errno on failure
 */
int sys_door_create(door_server_proc_t proc, void *cookie, uint32_t attr);

/**
 * Call a door
 *
 * @param fd        Door file descriptor
 * @param arg       Call arguments and result buffer
 * @return          0 on success, -errno on failure
 */
int sys_door_call(int fd, door_arg_t *arg);

/**
 * Return from a door invocation
 *
 * @param data      Return data
 * @param size      Return data size
 * @param descs     Descriptors to pass back
 * @param num_descs Number of descriptors
 * @return          Does not return on success, -errno on failure
 */
int sys_door_return(char *data, size_t size,
                    door_desc_t *descs, uint32_t num_descs);

/**
 * Get door info
 *
 * @param fd        Door file descriptor
 * @param info      Output info structure
 * @return          0 on success, -errno on failure
 */
int sys_door_info(int fd, door_info_t *info);

/**
 * Revoke a door
 *
 * @param fd        Door file descriptor
 * @return          0 on success, -errno on failure
 */
int sys_door_revoke(int fd);

/**
 * Get door credentials (caller info)
 *
 * @param info      Output credential info
 * @return          0 on success, -errno on failure
 */
int sys_door_cred(void *info);

/**
 * Bind door to file path
 *
 * @param fd        Door file descriptor
 * @param path      Filesystem path to bind
 * @return          0 on success, -errno on failure
 */
int sys_door_bind(int fd, const char *path);

/**
 * Unbind door from file path
 *
 * @param path      Filesystem path to unbind
 * @return          0 on success, -errno on failure
 */
int sys_door_unbind(const char *path);

/**
 * Get door parameter
 *
 * @param fd        Door file descriptor
 * @param param     Parameter to get (DOOR_PARAM_*)
 * @param out       Output value
 * @return          0 on success, -errno on failure
 */
int sys_door_getparam(int fd, int param, size_t *out);

/**
 * Set door parameter
 *
 * @param fd        Door file descriptor
 * @param param     Parameter to set (DOOR_PARAM_*)
 * @param value     Value to set
 * @return          0 on success, -errno on failure
 */
int sys_door_setparam(int fd, int param, size_t value);

/**
 * Initialize doors subsystem
 * Called once at boot after waitchan_init()
 */
void doors_init(void);

