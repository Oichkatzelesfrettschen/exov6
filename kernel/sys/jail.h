/**
 * @file jail.h
 * @brief FreeBSD-compatible Jail Interface
 *
 * Cleanroom implementation of jails for FeuerBird exokernel.
 * Uses isolation domains for actual isolation enforcement.
 *
 * Jails provide:
 * - Filesystem isolation (chroot on steroids)
 * - Network isolation (bound IP addresses)
 * - Process visibility isolation
 * - User and group mapping
 * - Resource limits
 */
#pragma once

#include <stdint.h>

/* size_t for kernel context */
#ifndef _SIZE_T_DEFINED
#define _SIZE_T_DEFINED
typedef unsigned long size_t;
#endif

/**
 * Jail ID type
 */
typedef int32_t jail_id_t;

/**
 * Jail API version
 */
#define JAIL_API_VERSION 2

/**
 * jail structure (FreeBSD-compatible)
 */
struct jail {
    uint32_t version;           /* Jail API version */
    char *path;                 /* Filesystem root */
    char *hostname;             /* Hostname */
    char *jailname;             /* Jail name (optional) */
    uint32_t ip4s;              /* Number of IPv4 addresses */
    uint32_t ip6s;              /* Number of IPv6 addresses */
    struct in_addr *ip4;        /* IPv4 addresses */
    struct in6_addr *ip6;       /* IPv6 addresses */
};

/**
 * jail_v2 flags
 */
#define JAIL_CREATE         0x01    /* Create jail */
#define JAIL_UPDATE         0x02    /* Update existing jail */
#define JAIL_ATTACH         0x04    /* Attach to jail */
#define JAIL_DYING          0x08    /* Jail is being removed */
#define JAIL_SET_MASK       0x0f    /* Valid flags for jail_set */
#define JAIL_GET_MASK       0x08    /* Valid flags for jail_get */

/**
 * Jail parameters (for jail_set/jail_get)
 */
#define JAIL_PARAM_JID              "jid"
#define JAIL_PARAM_NAME             "name"
#define JAIL_PARAM_PATH             "path"
#define JAIL_PARAM_HOSTNAME         "host.hostname"
#define JAIL_PARAM_IP4_ADDR         "ip4.addr"
#define JAIL_PARAM_IP6_ADDR         "ip6.addr"
#define JAIL_PARAM_SECURELEVEL      "securelevel"
#define JAIL_PARAM_DEVFS_RULESET    "devfs_ruleset"
#define JAIL_PARAM_CHILDREN_MAX     "children.max"
#define JAIL_PARAM_CHILDREN_CUR     "children.cur"
#define JAIL_PARAM_DYING            "dying"
#define JAIL_PARAM_PERSIST          "persist"
#define JAIL_PARAM_ALLOW_SET        "allow.set_hostname"
#define JAIL_PARAM_ALLOW_RAW        "allow.raw_sockets"
#define JAIL_PARAM_ALLOW_MOUNT      "allow.mount"

/**
 * iovec for jail_set/jail_get parameters
 */
struct iovec {
    void *iov_base;             /* Base address */
    size_t iov_len;             /* Length */
};

/**
 * Create and attach to a jail (legacy interface)
 *
 * @param jail      Jail specification
 * @return          Jail ID on success, -errno on failure
 */
int sys_jail(struct jail *jail);

/**
 * Attach to an existing jail
 *
 * @param jid       Jail ID
 * @return          0 on success, -errno on failure
 */
int sys_jail_attach(jail_id_t jid);

/**
 * Remove a jail
 *
 * @param jid       Jail ID
 * @return          0 on success, -errno on failure
 */
int sys_jail_remove(jail_id_t jid);

/**
 * Set jail parameters (modern interface)
 *
 * @param iov       Array of parameter name/value pairs
 * @param niov      Number of iovec entries (must be even)
 * @param flags     JAIL_* flags
 * @return          Jail ID on success, -errno on failure
 */
int sys_jail_set(struct iovec *iov, unsigned int niov, int flags);

/**
 * Get jail parameters
 *
 * @param iov       Array of parameter name/value pairs
 * @param niov      Number of iovec entries (must be even)
 * @param flags     JAIL_* flags
 * @return          Jail ID on success, -errno on failure
 */
int sys_jail_get(struct iovec *iov, unsigned int niov, int flags);

/**
 * Get current jail ID
 *
 * @return          Current jail ID (0 if not jailed)
 */
jail_id_t sys_jail_getid(void);

/**
 * Get jail name from ID
 *
 * @param jid       Jail ID
 * @param name      Output buffer for name
 * @param len       Buffer length
 * @return          0 on success, -errno on failure
 */
int sys_jail_getname(jail_id_t jid, char *name, size_t len);

/**
 * Initialize jail subsystem
 */
void jail_init(void);

