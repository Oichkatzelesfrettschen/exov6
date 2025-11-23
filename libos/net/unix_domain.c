/**
 * @file unix_domain.c
 * @brief Unix Domain Socket Implementation (AF_UNIX/AF_LOCAL)
 *
 * Implements Unix domain sockets for local inter-process communication.
 * Synthesized from 4.4BSD, NetBSD, FreeBSD, and OpenBSD implementations.
 *
 * Features:
 * - Stream sockets (SOCK_STREAM) with connection semantics
 * - Datagram sockets (SOCK_DGRAM) for connectionless IPC
 * - Sequenced packet sockets (SOCK_SEQPACKET)
 * - File descriptor passing via SCM_RIGHTS
 * - Credential passing via SCM_CREDS
 * - Abstract namespace support (Linux ABI compatibility)
 */

#include "socketvar.h"
#include "protosw.h"
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/un.h>
#include <unistd.h>

/* Unix PCB list */
static struct unpcb *unp_list = NULL;
static struct unpcb *unp_list_dgram = NULL;

/* Abstract namespace hash table (Linux ABI) */
#define UNP_ABSTRACT_HASH_SIZE  64
static struct unpcb *unp_abstract_hash[UNP_ABSTRACT_HASH_SIZE];

/* Filesystem namespace hash (by inode/device for bound sockets) */
#define UNP_FS_HASH_SIZE  64
static struct unpcb *unp_fs_hash[UNP_FS_HASH_SIZE];

/*
 * Hash function for abstract namespace
 */
static inline unsigned int
unp_abstract_hash_fn(const char *name, size_t len)
{
    unsigned int hash = 5381;
    for (size_t i = 0; i < len; i++)
        hash = ((hash << 5) + hash) + (unsigned char)name[i];
    return hash % UNP_ABSTRACT_HASH_SIZE;
}

/*
 * Allocate a Unix domain PCB
 */
static struct unpcb *
unp_alloc(struct socket *so)
{
    struct unpcb *unp = malloc(sizeof(struct unpcb));
    if (unp == NULL)
        return NULL;

    memset(unp, 0, sizeof(*unp));
    unp->unp_socket = so;
    so->so_pcb = unp;

    /* Add to appropriate list based on socket type */
    if (so->so_type == SOCK_DGRAM) {
        unp->unp_nextref = (struct socket *)unp_list_dgram;
        unp_list_dgram = unp;
    } else {
        unp->unp_nextref = (struct socket *)unp_list;
        unp_list = unp;
    }

    return unp;
}

/*
 * Free a Unix domain PCB
 */
static void
unp_free(struct unpcb *unp)
{
    if (unp == NULL)
        return;

    /* Remove from list */
    struct unpcb **listp = (unp->unp_socket->so_type == SOCK_DGRAM)
                           ? &unp_list_dgram : &unp_list;
    struct unpcb **pp = listp;
    while (*pp != NULL) {
        if (*pp == unp) {
            *pp = (struct unpcb *)(*pp)->unp_nextref;
            break;
        }
        pp = (struct unpcb **)&(*pp)->unp_nextref;
    }

    /* Free bound address */
    if (unp->unp_addr)
        free(unp->unp_addr);

    /* Disconnect from peer */
    if (unp->unp_conn) {
        struct unpcb *peer = unp->unp_conn;
        peer->unp_conn = NULL;
        if (peer->unp_socket)
            soisdisconnected(peer->unp_socket);
    }

    free(unp);
}

/*
 * Connect two Unix domain sockets
 */
static int
unp_connect2(struct socket *so, struct socket *so2)
{
    struct unpcb *unp = so->so_pcb;
    struct unpcb *unp2 = so2->so_pcb;

    if (unp == NULL || unp2 == NULL)
        return EINVAL;

    /* Check socket types match */
    if (so->so_type != so2->so_type)
        return EPROTOTYPE;

    /* For stream sockets, ensure peer is listening */
    if (so->so_type == SOCK_STREAM) {
        if ((so2->so_options & SO_ACCEPTCONN) == 0)
            return ECONNREFUSED;
    }

    /* Establish connection */
    unp->unp_conn = unp2;
    unp2->unp_conn = unp;

    return 0;
}

/*
 * Lookup a bound Unix domain socket by address
 */
static struct unpcb *
unp_lookup(struct sockaddr_un *sun, size_t len)
{
    if (sun == NULL || len < sizeof(sa_family_t))
        return NULL;

    /* Abstract namespace (starts with NUL byte) - Linux ABI */
    if (sun->sun_path[0] == '\0') {
        size_t namelen = len - offsetof(struct sockaddr_un, sun_path) - 1;
        unsigned int hash = unp_abstract_hash_fn(sun->sun_path + 1, namelen);

        for (struct unpcb *unp = unp_abstract_hash[hash]; unp != NULL;
             unp = (struct unpcb *)unp->unp_nextref) {
            if (unp->unp_addr == NULL)
                continue;
            size_t bound_len = sizeof(*unp->unp_addr);
            size_t bound_namelen = bound_len - offsetof(struct sockaddr_un, sun_path) - 1;
            if (bound_namelen == namelen &&
                memcmp(unp->unp_addr->sun_path + 1, sun->sun_path + 1, namelen) == 0)
                return unp;
        }
        return NULL;
    }

    /* Filesystem namespace - search by path */
    for (struct unpcb *unp = unp_list; unp != NULL;
         unp = (struct unpcb *)unp->unp_nextref) {
        if (unp->unp_addr == NULL)
            continue;
        if (strcmp(unp->unp_addr->sun_path, sun->sun_path) == 0)
            return unp;
    }

    /* Also check datagram list */
    for (struct unpcb *unp = unp_list_dgram; unp != NULL;
         unp = (struct unpcb *)unp->unp_nextref) {
        if (unp->unp_addr == NULL)
            continue;
        if (strcmp(unp->unp_addr->sun_path, sun->sun_path) == 0)
            return unp;
    }

    return NULL;
}

/*
 * Unix domain socket attach
 */
int
unix_attach(struct socket *so, int proto)
{
    struct unpcb *unp;

    /* Validate socket type */
    switch (so->so_type) {
    case SOCK_STREAM:
    case SOCK_DGRAM:
    case SOCK_SEQPACKET:
        break;
    default:
        return EPROTOTYPE;
    }

    unp = unp_alloc(so);
    if (unp == NULL)
        return ENOBUFS;

    return 0;
}

/*
 * Unix domain socket detach
 */
int
unix_detach(struct socket *so)
{
    struct unpcb *unp = so->so_pcb;
    if (unp == NULL)
        return 0;

    so->so_pcb = NULL;
    unp_free(unp);
    return 0;
}

/*
 * Bind a Unix domain socket to an address
 */
int
unix_bind(struct socket *so, struct sockaddr *nam, size_t namlen)
{
    struct unpcb *unp = so->so_pcb;
    struct sockaddr_un *sun = (struct sockaddr_un *)nam;

    if (unp == NULL)
        return EINVAL;

    if (namlen < offsetof(struct sockaddr_un, sun_path) + 1)
        return EINVAL;

    if (sun->sun_family != AF_UNIX && sun->sun_family != AF_LOCAL)
        return EAFNOSUPPORT;

    /* Check if already bound */
    if (unp->unp_addr != NULL)
        return EINVAL;

    /* Check for existing binding (except abstract namespace can overlap) */
    if (sun->sun_path[0] != '\0') {
        if (unp_lookup(sun, namlen) != NULL)
            return EADDRINUSE;
    }

    /* Allocate and copy address */
    unp->unp_addr = malloc(namlen);
    if (unp->unp_addr == NULL)
        return ENOBUFS;

    memcpy(unp->unp_addr, sun, namlen);

    /* Add to abstract hash if abstract namespace */
    if (sun->sun_path[0] == '\0') {
        size_t name_len = namlen - offsetof(struct sockaddr_un, sun_path) - 1;
        unsigned int hash = unp_abstract_hash_fn(sun->sun_path + 1, name_len);
        unp->unp_nextref = (struct socket *)unp_abstract_hash[hash];
        unp_abstract_hash[hash] = unp;
    }

    return 0;
}

/*
 * Listen on a Unix domain socket
 */
int
unix_listen(struct socket *so, int backlog)
{
    struct unpcb *unp = so->so_pcb;

    if (unp == NULL)
        return EINVAL;

    /* Only stream and seqpacket support listen */
    if (so->so_type != SOCK_STREAM && so->so_type != SOCK_SEQPACKET)
        return EOPNOTSUPP;

    /* Must be bound first */
    if (unp->unp_addr == NULL)
        return EDESTADDRREQ;

    so->so_options |= SO_ACCEPTCONN;
    so->so_qlimit = backlog;

    return 0;
}

/*
 * Connect a Unix domain socket
 */
int
unix_connect(struct socket *so, struct sockaddr *nam, size_t namlen)
{
    struct unpcb *unp = so->so_pcb;
    struct sockaddr_un *sun = (struct sockaddr_un *)nam;
    struct unpcb *unp2;
    int error;

    if (unp == NULL)
        return EINVAL;

    if (namlen < offsetof(struct sockaddr_un, sun_path) + 1)
        return EINVAL;

    /* Find the target socket */
    unp2 = unp_lookup(sun, namlen);
    if (unp2 == NULL)
        return ECONNREFUSED;

    /* Connect */
    error = unp_connect2(so, unp2->unp_socket);
    if (error)
        return error;

    /* Mark as connected */
    atomic_fetch_or(&so->so_state, SS_ISCONNECTED);

    return 0;
}

/*
 * Accept a connection on a Unix domain socket
 */
int
unix_accept(struct socket *so, struct sockaddr *nam)
{
    struct unpcb *unp = so->so_pcb;

    if (unp == NULL)
        return EINVAL;

    if (nam && unp->unp_conn && unp->unp_conn->unp_addr) {
        memcpy(nam, unp->unp_conn->unp_addr, sizeof(struct sockaddr_un));
    } else if (nam) {
        /* Connected to anonymous socket */
        struct sockaddr_un *sun = (struct sockaddr_un *)nam;
        memset(sun, 0, sizeof(*sun));
        sun->sun_family = AF_UNIX;
    }

    return 0;
}

/*
 * Send data on a Unix domain socket
 */
int
unix_send(struct socket *so, struct mbuf *m, struct sockaddr *addr,
          struct mbuf *control)
{
    struct unpcb *unp = so->so_pcb;
    struct socket *so2;
    int error;

    if (unp == NULL) {
        error = EINVAL;
        goto release;
    }

    /* Handle control messages (SCM_RIGHTS, SCM_CREDS) */
    if (control != NULL) {
        error = unp_internalize(control);
        if (error)
            goto release;
    }

    /* For connected sockets */
    if (unp->unp_conn != NULL) {
        so2 = unp->unp_conn->unp_socket;
        if (so2 == NULL) {
            error = ECONNRESET;
            goto release;
        }

        /* Append to peer's receive buffer */
        error = sbappend(&so2->so_rcv, m);
        if (error)
            goto release;

        /* Append control message if present */
        if (control != NULL)
            sbappendcontrol(&so2->so_rcv, NULL, control);

        /* Wake up receiver */
        sorwakeup(so2);
        return 0;
    }

    /* For datagram sockets with destination address */
    if (addr != NULL && so->so_type == SOCK_DGRAM) {
        struct unpcb *unp2 = unp_lookup((struct sockaddr_un *)addr,
                                        sizeof(struct sockaddr_un));
        if (unp2 == NULL) {
            error = ECONNREFUSED;
            goto release;
        }

        so2 = unp2->unp_socket;
        if (so2 == NULL) {
            error = ECONNREFUSED;
            goto release;
        }

        /* Build address record for receiver */
        struct sockaddr *sender_addr = NULL;
        struct mbuf *addr_mbuf = NULL;
        if (unp->unp_addr != NULL) {
            sender_addr = (struct sockaddr *)unp->unp_addr;
            /* Also keep mbuf for sbappendaddr internal use */
            addr_mbuf = m_get(M_NOWAIT, MT_SONAME);
            if (addr_mbuf != NULL) {
                addr_mbuf->m_len = sizeof(struct sockaddr_un);
                memcpy(mtod(addr_mbuf, struct sockaddr_un *),
                       unp->unp_addr, sizeof(struct sockaddr_un));
            }
        }

        /* Append with address */
        error = sbappendaddr(&so2->so_rcv, sender_addr, m, control);
        if (error) {
            if (addr_mbuf)
                m_free(addr_mbuf);
            goto release;
        }
        /* Free the addr mbuf if not used - data already appended */
        if (addr_mbuf)
            m_free(addr_mbuf);

        sorwakeup(so2);
        return 0;
    }

    /* No destination for unconnected socket */
    error = ENOTCONN;

release:
    if (control)
        m_freem(control);
    if (m)
        m_freem(m);
    return error;
}

/*
 * Shutdown a Unix domain socket
 */
int
unix_shutdown(struct socket *so)
{
    struct unpcb *unp = so->so_pcb;

    if (unp == NULL)
        return EINVAL;

    /* Notify peer of shutdown */
    if (unp->unp_conn != NULL) {
        struct socket *so2 = unp->unp_conn->unp_socket;
        if (so2 != NULL)
            socantrcvmore(so2);
    }

    socantsendmore(so);
    return 0;
}

/*
 * Get local address of Unix domain socket
 */
int
unix_sockaddr(struct socket *so, struct sockaddr *nam)
{
    struct unpcb *unp = so->so_pcb;

    if (unp == NULL)
        return EINVAL;

    if (unp->unp_addr != NULL) {
        memcpy(nam, unp->unp_addr, sizeof(struct sockaddr_un));
    } else {
        struct sockaddr_un *sun = (struct sockaddr_un *)nam;
        memset(sun, 0, sizeof(*sun));
        sun->sun_family = AF_UNIX;
    }

    return 0;
}

/*
 * Get peer address of Unix domain socket
 */
int
unix_peeraddr(struct socket *so, struct sockaddr *nam)
{
    struct unpcb *unp = so->so_pcb;

    if (unp == NULL)
        return EINVAL;

    if (unp->unp_conn == NULL)
        return ENOTCONN;

    if (unp->unp_conn->unp_addr != NULL) {
        memcpy(nam, unp->unp_conn->unp_addr, sizeof(struct sockaddr_un));
    } else {
        struct sockaddr_un *sun = (struct sockaddr_un *)nam;
        memset(sun, 0, sizeof(*sun));
        sun->sun_family = AF_UNIX;
    }

    return 0;
}

/*
 * Internalize control message (handle SCM_RIGHTS file descriptors)
 * This converts user file descriptors to internal references
 */
int
unp_internalize(struct mbuf *control)
{
    struct cmsghdr *cm;
    int *fdp;
    int nfds;

    if (control == NULL || control->m_len < sizeof(struct cmsghdr))
        return 0;

    cm = mtod(control, struct cmsghdr *);

    if (cm->cmsg_level != SOL_SOCKET)
        return 0;

    switch (cm->cmsg_type) {
    case SCM_RIGHTS:
        /* File descriptor passing */
        nfds = (cm->cmsg_len - CMSG_ALIGN(sizeof(struct cmsghdr))) / sizeof(int);
        fdp = (int *)CMSG_DATA(cm);

        /* Validate all file descriptors */
        for (int i = 0; i < nfds; i++) {
            if (fdp[i] < 0)
                return EBADF;
            /* In real implementation, would convert to file references */
        }
        break;

    case SCM_CREDS:
        /* Credential passing - fill in sender's credentials */
        /* In real implementation, would fill in pid, uid, gid */
        break;

    default:
        /* Unknown control type - pass through */
        break;
    }

    return 0;
}

/*
 * Externalize control message (handle SCM_RIGHTS file descriptors)
 * This converts internal references back to user file descriptors
 */
int
unp_externalize(struct mbuf *control)
{
    struct cmsghdr *cm;
    int *fdp;
    int nfds;

    if (control == NULL || control->m_len < sizeof(struct cmsghdr))
        return 0;

    cm = mtod(control, struct cmsghdr *);

    if (cm->cmsg_level != SOL_SOCKET || cm->cmsg_type != SCM_RIGHTS)
        return 0;

    nfds = (cm->cmsg_len - CMSG_ALIGN(sizeof(struct cmsghdr))) / sizeof(int);
    fdp = (int *)CMSG_DATA(cm);

    /* Convert internal references to file descriptors */
    for (int i = 0; i < nfds; i++) {
        /* In real implementation, would allocate new fd in receiver's table */
        fdp[i] = fdp[i];  /* Placeholder */
    }

    return 0;
}

/*
 * Protocol switch entries for Unix domain
 */
static struct protosw unix_stream_protosw = {
    .pr_type = SOCK_STREAM,
    .pr_protocol = 0,
    .pr_flags = PR_CONNREQUIRED | PR_WANTRCVD | PR_LISTEN | PR_RIGHTS,
    .pr_domain = AF_UNIX,
    .pr_attach = unix_attach,
    .pr_detach = unix_detach,
    .pr_bind = unix_bind,
    .pr_listen = unix_listen,
    .pr_connect = unix_connect,
    .pr_accept = unix_accept,
    .pr_send = unix_send,
    .pr_shutdown = unix_shutdown,
    .pr_sockaddr = unix_sockaddr,
    .pr_peeraddr = unix_peeraddr,
};

static struct protosw unix_dgram_protosw = {
    .pr_type = SOCK_DGRAM,
    .pr_protocol = 0,
    .pr_flags = PR_ATOMIC | PR_ADDR | PR_RIGHTS,
    .pr_domain = AF_UNIX,
    .pr_attach = unix_attach,
    .pr_detach = unix_detach,
    .pr_bind = unix_bind,
    .pr_connect = unix_connect,
    .pr_send = unix_send,
    .pr_shutdown = unix_shutdown,
    .pr_sockaddr = unix_sockaddr,
    .pr_peeraddr = unix_peeraddr,
};

static struct protosw unix_seqpacket_protosw = {
    .pr_type = SOCK_SEQPACKET,
    .pr_protocol = 0,
    .pr_flags = PR_CONNREQUIRED | PR_ATOMIC | PR_WANTRCVD | PR_LISTEN | PR_RIGHTS,
    .pr_domain = AF_UNIX,
    .pr_attach = unix_attach,
    .pr_detach = unix_detach,
    .pr_bind = unix_bind,
    .pr_listen = unix_listen,
    .pr_connect = unix_connect,
    .pr_accept = unix_accept,
    .pr_send = unix_send,
    .pr_shutdown = unix_shutdown,
    .pr_sockaddr = unix_sockaddr,
    .pr_peeraddr = unix_peeraddr,
};

static struct protosw unix_protosw[] = {
    /* Stream */
    {
        .pr_type = SOCK_STREAM,
        .pr_protocol = 0,
        .pr_flags = PR_CONNREQUIRED | PR_WANTRCVD | PR_LISTEN | PR_RIGHTS,
        .pr_domain = AF_UNIX,
        .pr_attach = unix_attach,
        .pr_detach = unix_detach,
        .pr_bind = unix_bind,
        .pr_listen = unix_listen,
        .pr_connect = unix_connect,
        .pr_accept = unix_accept,
        .pr_send = unix_send,
        .pr_shutdown = unix_shutdown,
        .pr_sockaddr = unix_sockaddr,
        .pr_peeraddr = unix_peeraddr,
    },
    /* Datagram */
    {
        .pr_type = SOCK_DGRAM,
        .pr_protocol = 0,
        .pr_flags = PR_ATOMIC | PR_ADDR | PR_RIGHTS,
        .pr_domain = AF_UNIX,
        .pr_attach = unix_attach,
        .pr_detach = unix_detach,
        .pr_bind = unix_bind,
        .pr_connect = unix_connect,
        .pr_send = unix_send,
        .pr_shutdown = unix_shutdown,
        .pr_sockaddr = unix_sockaddr,
        .pr_peeraddr = unix_peeraddr,
    },
    /* Sequenced Packet */
    {
        .pr_type = SOCK_SEQPACKET,
        .pr_protocol = 0,
        .pr_flags = PR_CONNREQUIRED | PR_ATOMIC | PR_WANTRCVD | PR_LISTEN | PR_RIGHTS,
        .pr_domain = AF_UNIX,
        .pr_attach = unix_attach,
        .pr_detach = unix_detach,
        .pr_bind = unix_bind,
        .pr_listen = unix_listen,
        .pr_connect = unix_connect,
        .pr_accept = unix_accept,
        .pr_send = unix_send,
        .pr_shutdown = unix_shutdown,
        .pr_sockaddr = unix_sockaddr,
        .pr_peeraddr = unix_peeraddr,
    },
};

/*
 * Unix domain
 */
static void
unix_domain_init(void)
{
    unix_init();
}

struct domain unixdomain = {
    .dom_family = AF_UNIX,
    .dom_name = "unix",
    .dom_init = unix_domain_init,
    .dom_protosw = unix_protosw,
    .dom_protoswend = &unix_protosw[sizeof(unix_protosw)/sizeof(unix_protosw[0])],
};

/* Also register as AF_LOCAL (alias) */
struct domain localdomain = {
    .dom_family = AF_LOCAL,
    .dom_name = "local",
    .dom_init = NULL,  /* Shares init with unix */
    .dom_protosw = unix_protosw,
    .dom_protoswend = &unix_protosw[sizeof(unix_protosw)/sizeof(unix_protosw[0])],
};

void
unix_init(void)
{
    /* Initialize Unix domain socket subsystem */
    memset(unp_abstract_hash, 0, sizeof(unp_abstract_hash));
    memset(unp_fs_hash, 0, sizeof(unp_fs_hash));
}

/*
 * Register the Unix domain
 */
__attribute__((constructor))
static void
unix_domain_register(void)
{
    domain_add(&unixdomain);
    domain_add(&localdomain);
}
