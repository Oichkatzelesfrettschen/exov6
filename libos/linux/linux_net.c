/**
 * @file linux_net.c
 * @brief Linux network syscall implementations
 *
 * This file bridges Linux network syscalls to the BSD socket implementation.
 * Provides socket, bind, connect, listen, accept, send, recv, and related ops.
 *
 * Linux uses individual syscalls for network operations (unlike BSD socketcall).
 * This layer translates Linux conventions to BSD socket internals.
 */

#include "linux_syscall.h"
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/*============================================================================
 * Linux Socket Constants
 *============================================================================*/

/* Address families */
#define AF_UNSPEC       0
#define AF_UNIX         1
#define AF_LOCAL        AF_UNIX
#define AF_INET         2
#define AF_INET6        10
#define AF_NETLINK      16
#define AF_PACKET       17

/* Socket types */
#define SOCK_STREAM     1
#define SOCK_DGRAM      2
#define SOCK_RAW        3
#define SOCK_RDM        4
#define SOCK_SEQPACKET  5
#define SOCK_DCCP       6
#define SOCK_PACKET     10

/* Socket type flags */
#define SOCK_CLOEXEC    02000000
#define SOCK_NONBLOCK   00004000

/* Protocol families */
#define PF_UNSPEC       AF_UNSPEC
#define PF_UNIX         AF_UNIX
#define PF_LOCAL        AF_LOCAL
#define PF_INET         AF_INET
#define PF_INET6        AF_INET6

/* Protocols */
#define IPPROTO_IP      0
#define IPPROTO_ICMP    1
#define IPPROTO_TCP     6
#define IPPROTO_UDP     17
#define IPPROTO_RAW     255

/* Shutdown modes */
#define SHUT_RD         0
#define SHUT_WR         1
#define SHUT_RDWR       2

/* Socket options levels */
#define SOL_SOCKET      1
#define SOL_IP          0
#define SOL_TCP         6
#define SOL_UDP         17
#define SOL_IPV6        41

/* Socket options (SOL_SOCKET) */
#define SO_DEBUG        1
#define SO_REUSEADDR    2
#define SO_TYPE         3
#define SO_ERROR        4
#define SO_DONTROUTE    5
#define SO_BROADCAST    6
#define SO_SNDBUF       7
#define SO_RCVBUF       8
#define SO_KEEPALIVE    9
#define SO_OOBINLINE    10
#define SO_NO_CHECK     11
#define SO_PRIORITY     12
#define SO_LINGER       13
#define SO_BSDCOMPAT    14
#define SO_REUSEPORT    15
#define SO_PASSCRED     16
#define SO_PEERCRED     17
#define SO_RCVLOWAT     18
#define SO_SNDLOWAT     19
#define SO_RCVTIMEO     20
#define SO_SNDTIMEO     21
#define SO_ACCEPTCONN   30
#define SO_PEERNAME     28
#define SO_TIMESTAMP    29
#define SO_DOMAIN       39
#define SO_PROTOCOL     38
#define SO_BINDTODEVICE 25

/* TCP options */
#define TCP_NODELAY     1
#define TCP_MAXSEG      2
#define TCP_CORK        3
#define TCP_KEEPIDLE    4
#define TCP_KEEPINTVL   5
#define TCP_KEEPCNT     6
#define TCP_SYNCNT      7
#define TCP_LINGER2     8
#define TCP_DEFER_ACCEPT 9
#define TCP_WINDOW_CLAMP 10
#define TCP_INFO        11
#define TCP_QUICKACK    12
#define TCP_CONGESTION  13
#define TCP_FASTOPEN    23

/* Message flags */
#define MSG_OOB         0x01
#define MSG_PEEK        0x02
#define MSG_DONTROUTE   0x04
#define MSG_TRYHARD     MSG_DONTROUTE
#define MSG_CTRUNC      0x08
#define MSG_PROXY       0x10
#define MSG_TRUNC       0x20
#define MSG_DONTWAIT    0x40
#define MSG_EOR         0x80
#define MSG_WAITALL     0x100
#define MSG_FIN         0x200
#define MSG_SYN         0x400
#define MSG_CONFIRM     0x800
#define MSG_RST         0x1000
#define MSG_ERRQUEUE    0x2000
#define MSG_NOSIGNAL    0x4000
#define MSG_MORE        0x8000
#define MSG_WAITFORONE  0x10000
#define MSG_BATCH       0x40000
#define MSG_FASTOPEN    0x20000000
#define MSG_CMSG_CLOEXEC 0x40000000

/*============================================================================
 * Socket Address Structures
 *============================================================================*/

/* Generic socket address */
struct sockaddr {
    uint16_t sa_family;
    char sa_data[14];
};

/* IPv4 address */
struct sockaddr_in {
    uint16_t sin_family;
    uint16_t sin_port;
    uint32_t sin_addr;
    uint8_t  sin_zero[8];
};

/* IPv6 address */
struct sockaddr_in6 {
    uint16_t sin6_family;
    uint16_t sin6_port;
    uint32_t sin6_flowinfo;
    uint8_t  sin6_addr[16];
    uint32_t sin6_scope_id;
};

/* Unix domain address */
struct sockaddr_un {
    uint16_t sun_family;
    char sun_path[108];
};

/* Storage (large enough for any address) */
struct sockaddr_storage {
    uint16_t ss_family;
    char __ss_padding[126];
};

/*============================================================================
 * Message Header Structures
 *============================================================================*/

struct msghdr {
    void *msg_name;             /* Socket address */
    uint32_t msg_namelen;       /* Address length */
    struct linux_iovec *msg_iov; /* Scatter/gather array */
    size_t msg_iovlen;          /* # elements in msg_iov */
    void *msg_control;          /* Ancillary data */
    size_t msg_controllen;      /* Ancillary data length */
    int msg_flags;              /* Flags on received message */
};

struct mmsghdr {
    struct msghdr msg_hdr;      /* Message header */
    unsigned int msg_len;       /* Bytes transmitted */
};

struct cmsghdr {
    size_t cmsg_len;            /* Data length including header */
    int cmsg_level;             /* Originating protocol */
    int cmsg_type;              /* Protocol-specific type */
    /* Followed by data */
};

/*============================================================================
 * Socket State Management
 *============================================================================*/

/* Socket state */
struct linux_socket {
    int fd;                     /* Linux file descriptor */
    int domain;                 /* Address family */
    int type;                   /* Socket type */
    int protocol;               /* Protocol */
    int flags;                  /* Socket flags */
    int state;                  /* Connection state */
    int bsd_fd;                 /* BSD socket file descriptor */

    /* Socket options */
    int so_reuseaddr;
    int so_reuseport;
    int so_keepalive;
    int so_broadcast;
    int so_sndbuf;
    int so_rcvbuf;
    struct linux_timeval so_sndtimeo;
    struct linux_timeval so_rcvtimeo;

    /* Bound/connected addresses */
    struct sockaddr_storage local_addr;
    socklen_t local_addrlen;
    struct sockaddr_storage peer_addr;
    socklen_t peer_addrlen;

    bool in_use;
};

typedef unsigned int socklen_t;

/* Socket state constants */
#define SS_FREE         0
#define SS_UNCONNECTED  1
#define SS_CONNECTING   2
#define SS_CONNECTED    3
#define SS_DISCONNECTING 4
#define SS_LISTENING    5

/* Socket table */
#define LINUX_SOCKET_MAX 1024
static struct linux_socket linux_sockets[LINUX_SOCKET_MAX];
static int socket_next_fd = 3;  /* Start after stdin/stdout/stderr */

/*============================================================================
 * BSD Socket Layer Interface
 *============================================================================*/

/* Forward declarations for BSD socket layer */
extern int bsd_socket(int domain, int type, int protocol);
extern int bsd_bind(int fd, const struct sockaddr *addr, socklen_t addrlen);
extern int bsd_listen(int fd, int backlog);
extern int bsd_accept(int fd, struct sockaddr *addr, socklen_t *addrlen);
extern int bsd_connect(int fd, const struct sockaddr *addr, socklen_t addrlen);
extern ssize_t bsd_sendto(int fd, const void *buf, size_t len, int flags,
                          const struct sockaddr *dest_addr, socklen_t addrlen);
extern ssize_t bsd_recvfrom(int fd, void *buf, size_t len, int flags,
                            struct sockaddr *src_addr, socklen_t *addrlen);
extern int bsd_shutdown(int fd, int how);
extern int bsd_close(int fd);
extern int bsd_getsockopt(int fd, int level, int optname, void *optval,
                          socklen_t *optlen);
extern int bsd_setsockopt(int fd, int level, int optname, const void *optval,
                          socklen_t optlen);
extern int bsd_getsockname(int fd, struct sockaddr *addr, socklen_t *addrlen);
extern int bsd_getpeername(int fd, struct sockaddr *addr, socklen_t *addrlen);
extern int bsd_socketpair(int domain, int type, int protocol, int sv[2]);

/*============================================================================
 * Helper Functions
 *============================================================================*/

/**
 * Find socket by Linux fd
 */
static struct linux_socket *find_socket(int fd)
{
    for (int i = 0; i < LINUX_SOCKET_MAX; i++) {
        if (linux_sockets[i].in_use && linux_sockets[i].fd == fd) {
            return &linux_sockets[i];
        }
    }
    return NULL;
}

/**
 * Allocate a new socket
 */
static struct linux_socket *alloc_socket(void)
{
    for (int i = 0; i < LINUX_SOCKET_MAX; i++) {
        if (!linux_sockets[i].in_use) {
            linux_sockets[i].in_use = true;
            linux_sockets[i].fd = socket_next_fd++;
            linux_sockets[i].state = SS_UNCONNECTED;
            linux_sockets[i].so_sndbuf = 65536;
            linux_sockets[i].so_rcvbuf = 65536;
            return &linux_sockets[i];
        }
    }
    return NULL;
}

/**
 * Free a socket
 */
static void free_socket(struct linux_socket *sock)
{
    if (sock) {
        sock->in_use = false;
    }
}

/*============================================================================
 * Socket Creation/Destruction
 *============================================================================*/

/**
 * Create a socket
 */
long linux_sys_socket(int domain, int type, int protocol)
{
    /* Extract type flags */
    int type_flags = type & ~0xFF;
    type = type & 0xFF;

    /* Validate domain */
    switch (domain) {
    case AF_UNIX:
    case AF_INET:
    case AF_INET6:
        break;
    default:
        return -LINUX_EAFNOSUPPORT;
    }

    /* Validate type */
    switch (type) {
    case SOCK_STREAM:
    case SOCK_DGRAM:
    case SOCK_RAW:
    case SOCK_SEQPACKET:
        break;
    default:
        return -LINUX_ESOCKTNOSUPPORT;
    }

    /* Allocate socket structure */
    struct linux_socket *sock = alloc_socket();
    if (!sock) {
        return -LINUX_ENFILE;
    }

    sock->domain = domain;
    sock->type = type;
    sock->protocol = protocol;
    sock->flags = type_flags;

    /* Create BSD socket */
    int bsd_fd = bsd_socket(domain, type, protocol);
    if (bsd_fd < 0) {
        free_socket(sock);
        return bsd_fd;
    }
    sock->bsd_fd = bsd_fd;

    /* Apply type flags */
    if (type_flags & SOCK_NONBLOCK) {
        /* TODO: Set non-blocking */
    }
    if (type_flags & SOCK_CLOEXEC) {
        /* TODO: Set close-on-exec */
    }

    return sock->fd;
}

/**
 * Create a socket pair
 */
long linux_sys_socketpair(int domain, int type, int protocol, int sv[2])
{
    if (!sv) {
        return -LINUX_EFAULT;
    }

    int type_flags = type & ~0xFF;
    type = type & 0xFF;

    /* Only Unix domain supports socketpair */
    if (domain != AF_UNIX) {
        return -LINUX_EOPNOTSUPP;
    }

    /* Allocate two sockets */
    struct linux_socket *sock1 = alloc_socket();
    struct linux_socket *sock2 = alloc_socket();

    if (!sock1 || !sock2) {
        if (sock1) free_socket(sock1);
        if (sock2) free_socket(sock2);
        return -LINUX_ENFILE;
    }

    /* Create BSD socketpair */
    int bsd_sv[2];
    int ret = bsd_socketpair(domain, type, protocol, bsd_sv);
    if (ret < 0) {
        free_socket(sock1);
        free_socket(sock2);
        return ret;
    }

    sock1->domain = domain;
    sock1->type = type;
    sock1->protocol = protocol;
    sock1->flags = type_flags;
    sock1->bsd_fd = bsd_sv[0];
    sock1->state = SS_CONNECTED;

    sock2->domain = domain;
    sock2->type = type;
    sock2->protocol = protocol;
    sock2->flags = type_flags;
    sock2->bsd_fd = bsd_sv[1];
    sock2->state = SS_CONNECTED;

    sv[0] = sock1->fd;
    sv[1] = sock2->fd;

    return 0;
}

/*============================================================================
 * Socket Binding/Listening
 *============================================================================*/

/**
 * Bind socket to address
 */
long linux_sys_bind(int sockfd, const struct sockaddr *addr, socklen_t addrlen)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    if (!addr) {
        return -LINUX_EFAULT;
    }

    int ret = bsd_bind(sock->bsd_fd, addr, addrlen);
    if (ret < 0) {
        return ret;
    }

    /* Store local address */
    if (addrlen <= sizeof(sock->local_addr)) {
        for (socklen_t i = 0; i < addrlen; i++) {
            ((char *)&sock->local_addr)[i] = ((char *)addr)[i];
        }
        sock->local_addrlen = addrlen;
    }

    return 0;
}

/**
 * Listen for connections
 */
long linux_sys_listen(int sockfd, int backlog)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    if (sock->type != SOCK_STREAM && sock->type != SOCK_SEQPACKET) {
        return -LINUX_EOPNOTSUPP;
    }

    int ret = bsd_listen(sock->bsd_fd, backlog);
    if (ret < 0) {
        return ret;
    }

    sock->state = SS_LISTENING;
    return 0;
}

/*============================================================================
 * Connection Operations
 *============================================================================*/

/**
 * Accept a connection
 */
long linux_sys_accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen)
{
    return linux_sys_accept4(sockfd, addr, addrlen, 0);
}

/**
 * Accept a connection with flags
 */
long linux_sys_accept4(int sockfd, struct sockaddr *addr, socklen_t *addrlen,
                       int flags)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    if (sock->state != SS_LISTENING) {
        return -LINUX_EINVAL;
    }

    int bsd_client = bsd_accept(sock->bsd_fd, addr, addrlen);
    if (bsd_client < 0) {
        return bsd_client;
    }

    /* Create new socket for client */
    struct linux_socket *client = alloc_socket();
    if (!client) {
        bsd_close(bsd_client);
        return -LINUX_ENFILE;
    }

    client->domain = sock->domain;
    client->type = sock->type;
    client->protocol = sock->protocol;
    client->flags = flags;
    client->bsd_fd = bsd_client;
    client->state = SS_CONNECTED;

    /* Copy peer address */
    if (addr && addrlen && *addrlen <= sizeof(client->peer_addr)) {
        for (socklen_t i = 0; i < *addrlen; i++) {
            ((char *)&client->peer_addr)[i] = ((char *)addr)[i];
        }
        client->peer_addrlen = *addrlen;
    }

    return client->fd;
}

/**
 * Connect to a server
 */
long linux_sys_connect(int sockfd, const struct sockaddr *addr, socklen_t addrlen)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    if (!addr) {
        return -LINUX_EFAULT;
    }

    sock->state = SS_CONNECTING;

    int ret = bsd_connect(sock->bsd_fd, addr, addrlen);
    if (ret < 0) {
        sock->state = SS_UNCONNECTED;
        return ret;
    }

    sock->state = SS_CONNECTED;

    /* Store peer address */
    if (addrlen <= sizeof(sock->peer_addr)) {
        for (socklen_t i = 0; i < addrlen; i++) {
            ((char *)&sock->peer_addr)[i] = ((char *)addr)[i];
        }
        sock->peer_addrlen = addrlen;
    }

    return 0;
}

/*============================================================================
 * Data Transfer
 *============================================================================*/

/**
 * Send data on socket
 */
long linux_sys_sendto(int sockfd, const void *buf, size_t len, int flags,
                      const struct sockaddr *dest_addr, socklen_t addrlen)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    if (!buf && len > 0) {
        return -LINUX_EFAULT;
    }

    return bsd_sendto(sock->bsd_fd, buf, len, flags, dest_addr, addrlen);
}

/**
 * Send data (connected socket)
 */
long linux_sys_send(int sockfd, const void *buf, size_t len, int flags)
{
    return linux_sys_sendto(sockfd, buf, len, flags, NULL, 0);
}

/**
 * Receive data from socket
 */
long linux_sys_recvfrom(int sockfd, void *buf, size_t len, int flags,
                        struct sockaddr *src_addr, socklen_t *addrlen)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    if (!buf && len > 0) {
        return -LINUX_EFAULT;
    }

    return bsd_recvfrom(sock->bsd_fd, buf, len, flags, src_addr, addrlen);
}

/**
 * Receive data (connected socket)
 */
long linux_sys_recv(int sockfd, void *buf, size_t len, int flags)
{
    return linux_sys_recvfrom(sockfd, buf, len, flags, NULL, NULL);
}

/*============================================================================
 * Message Operations
 *============================================================================*/

/**
 * Send message
 */
long linux_sys_sendmsg(int sockfd, const struct msghdr *msg, int flags)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    if (!msg) {
        return -LINUX_EFAULT;
    }

    /* Compute total length */
    size_t total = 0;
    for (size_t i = 0; i < msg->msg_iovlen; i++) {
        total += msg->msg_iov[i].iov_len;
    }

    /* Send each iovec */
    ssize_t sent = 0;
    for (size_t i = 0; i < msg->msg_iovlen; i++) {
        ssize_t n = bsd_sendto(sock->bsd_fd, msg->msg_iov[i].iov_base,
                               msg->msg_iov[i].iov_len, flags,
                               msg->msg_name, msg->msg_namelen);
        if (n < 0) {
            return (sent > 0) ? sent : n;
        }
        sent += n;
        if ((size_t)n < msg->msg_iov[i].iov_len) break;
    }

    return sent;
}

/**
 * Receive message
 */
long linux_sys_recvmsg(int sockfd, struct msghdr *msg, int flags)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    if (!msg) {
        return -LINUX_EFAULT;
    }

    /* Receive into iovecs */
    ssize_t total = 0;
    for (size_t i = 0; i < msg->msg_iovlen; i++) {
        socklen_t addrlen = msg->msg_namelen;
        ssize_t n = bsd_recvfrom(sock->bsd_fd, msg->msg_iov[i].iov_base,
                                 msg->msg_iov[i].iov_len, flags,
                                 msg->msg_name, &addrlen);
        if (n < 0) {
            return (total > 0) ? total : n;
        }
        if (i == 0) {
            msg->msg_namelen = addrlen;
        }
        total += n;
        if ((size_t)n < msg->msg_iov[i].iov_len) break;
    }

    return total;
}

/**
 * Send multiple messages
 */
long linux_sys_sendmmsg(int sockfd, struct mmsghdr *msgvec, unsigned int vlen,
                        int flags)
{
    if (!msgvec) {
        return -LINUX_EFAULT;
    }

    unsigned int sent = 0;
    for (unsigned int i = 0; i < vlen; i++) {
        ssize_t n = linux_sys_sendmsg(sockfd, &msgvec[i].msg_hdr, flags);
        if (n < 0) {
            return (sent > 0) ? sent : n;
        }
        msgvec[i].msg_len = n;
        sent++;
    }

    return sent;
}

/**
 * Receive multiple messages
 */
long linux_sys_recvmmsg(int sockfd, struct mmsghdr *msgvec, unsigned int vlen,
                        int flags, struct linux_timespec *timeout)
{
    if (!msgvec) {
        return -LINUX_EFAULT;
    }

    (void)timeout;  /* TODO: Implement timeout */

    unsigned int received = 0;
    for (unsigned int i = 0; i < vlen; i++) {
        ssize_t n = linux_sys_recvmsg(sockfd, &msgvec[i].msg_hdr, flags);
        if (n < 0) {
            return (received > 0) ? received : n;
        }
        msgvec[i].msg_len = n;
        received++;

        if (flags & MSG_WAITFORONE) {
            flags |= MSG_DONTWAIT;
        }
    }

    return received;
}

/*============================================================================
 * Socket Control
 *============================================================================*/

/**
 * Shutdown socket
 */
long linux_sys_shutdown(int sockfd, int how)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    int ret = bsd_shutdown(sock->bsd_fd, how);
    if (ret < 0) {
        return ret;
    }

    if (how == SHUT_RDWR) {
        sock->state = SS_DISCONNECTING;
    }

    return 0;
}

/**
 * Close socket
 */
long linux_sys_socket_close(int sockfd)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    bsd_close(sock->bsd_fd);
    free_socket(sock);

    return 0;
}

/*============================================================================
 * Socket Options
 *============================================================================*/

/**
 * Get socket option
 */
long linux_sys_getsockopt(int sockfd, int level, int optname, void *optval,
                          socklen_t *optlen)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    return bsd_getsockopt(sock->bsd_fd, level, optname, optval, optlen);
}

/**
 * Set socket option
 */
long linux_sys_setsockopt(int sockfd, int level, int optname, const void *optval,
                          socklen_t optlen)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    /* Cache some options locally */
    if (level == SOL_SOCKET) {
        switch (optname) {
        case SO_REUSEADDR:
            if (optval && optlen >= sizeof(int)) {
                sock->so_reuseaddr = *(int *)optval;
            }
            break;
        case SO_REUSEPORT:
            if (optval && optlen >= sizeof(int)) {
                sock->so_reuseport = *(int *)optval;
            }
            break;
        case SO_SNDBUF:
            if (optval && optlen >= sizeof(int)) {
                sock->so_sndbuf = *(int *)optval;
            }
            break;
        case SO_RCVBUF:
            if (optval && optlen >= sizeof(int)) {
                sock->so_rcvbuf = *(int *)optval;
            }
            break;
        }
    }

    return bsd_setsockopt(sock->bsd_fd, level, optname, optval, optlen);
}

/*============================================================================
 * Socket Address Operations
 *============================================================================*/

/**
 * Get local address
 */
long linux_sys_getsockname(int sockfd, struct sockaddr *addr, socklen_t *addrlen)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    return bsd_getsockname(sock->bsd_fd, addr, addrlen);
}

/**
 * Get peer address
 */
long linux_sys_getpeername(int sockfd, struct sockaddr *addr, socklen_t *addrlen)
{
    struct linux_socket *sock = find_socket(sockfd);
    if (!sock) {
        return -LINUX_EBADF;
    }

    return bsd_getpeername(sock->bsd_fd, addr, addrlen);
}

/*============================================================================
 * Debugging Interface
 *============================================================================*/

/**
 * Get socket statistics
 */
int linux_get_socket_stats(int *active_sockets, int *listening, int *connected)
{
    int active = 0, listen = 0, conn = 0;

    for (int i = 0; i < LINUX_SOCKET_MAX; i++) {
        if (linux_sockets[i].in_use) {
            active++;
            if (linux_sockets[i].state == SS_LISTENING) {
                listen++;
            } else if (linux_sockets[i].state == SS_CONNECTED) {
                conn++;
            }
        }
    }

    if (active_sockets) *active_sockets = active;
    if (listening) *listening = listen;
    if (connected) *connected = conn;

    return 0;
}
