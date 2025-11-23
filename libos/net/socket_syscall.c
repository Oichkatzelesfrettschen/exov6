/**
 * @file socket_syscall.c
 * @brief Socket System Call Interface
 *
 * Bridges POSIX/Linux socket API to BSD socket internals.
 * Implements the syscall handlers for socket operations.
 */

#include "socketvar.h"
#include "protosw.h"
#include "../file.h"
#include <errno.h>
#include <string.h>
#include <stdlib.h>

/* Linux-style socket flags (not always available on BSD/macOS) */
#ifndef SOCK_NONBLOCK
#define SOCK_NONBLOCK   0x800
#endif
#ifndef SOCK_CLOEXEC
#define SOCK_CLOEXEC    0x80000
#endif

/* Maximum number of sockets */
#define MAX_SOCKETS     1024

/* Forward declarations */
ssize_t sys_sendto(int fd, const void *buf, size_t len, int flags,
                   const struct sockaddr *dest_addr, socklen_t addrlen);
ssize_t sys_recvfrom(int fd, void *buf, size_t len, int flags,
                     struct sockaddr *src_addr, socklen_t *addrlen);

/* Socket table - maps fd to socket */
static struct {
    struct socket *sock;
    int flags;
} socket_table[MAX_SOCKETS];

static int socket_next_fd = 3;  /* Start after stdin/stdout/stderr */

/*
 * Allocate a socket descriptor
 */
static int
socket_alloc_fd(struct socket *so)
{
    for (int i = socket_next_fd; i < MAX_SOCKETS; i++) {
        if (socket_table[i].sock == NULL) {
            socket_table[i].sock = so;
            socket_table[i].flags = 0;
            socket_next_fd = i + 1;
            return i;
        }
    }
    /* Wrap around and try from beginning */
    for (int i = 3; i < socket_next_fd; i++) {
        if (socket_table[i].sock == NULL) {
            socket_table[i].sock = so;
            socket_table[i].flags = 0;
            return i;
        }
    }
    return -1;
}

/*
 * Get socket from file descriptor
 */
static struct socket *
socket_from_fd(int fd)
{
    if (fd < 0 || fd >= MAX_SOCKETS)
        return NULL;
    return socket_table[fd].sock;
}

/*
 * Free a socket descriptor
 */
static void
socket_free_fd(int fd)
{
    if (fd >= 0 && fd < MAX_SOCKETS) {
        socket_table[fd].sock = NULL;
        socket_table[fd].flags = 0;
    }
}

/*
 * POSIX socket(2)
 */
int
sys_socket(int domain, int type, int protocol)
{
    struct socket *so;
    int error;

    /* Handle type flags (Linux-style SOCK_NONBLOCK, SOCK_CLOEXEC) */
    int flags = type & (SOCK_NONBLOCK | SOCK_CLOEXEC);
    type &= ~(SOCK_NONBLOCK | SOCK_CLOEXEC);

    error = socreate(domain, &so, type, protocol);
    if (error)
        return -error;

    /* Apply flags */
    if (flags & SOCK_NONBLOCK)
        so->so_state |= SS_NBIO;

    int fd = socket_alloc_fd(so);
    if (fd < 0) {
        soclose(so);
        return -EMFILE;
    }

    socket_table[fd].flags = flags;
    return fd;
}

/*
 * POSIX socketpair(2)
 */
int
sys_socketpair(int domain, int type, int protocol, int sv[2])
{
    struct socket *so1, *so2;
    int error;
    int flags = type & (SOCK_NONBLOCK | SOCK_CLOEXEC);
    type &= ~(SOCK_NONBLOCK | SOCK_CLOEXEC);

    /* Only AF_UNIX supports socketpair */
    if (domain != AF_UNIX)
        return -EOPNOTSUPP;

    error = socreate(domain, &so1, type, protocol);
    if (error)
        return -error;

    error = socreate(domain, &so2, type, protocol);
    if (error) {
        soclose(so1);
        return -error;
    }

    /* Connect them via protocol */
    if (so1->so_proto->pr_usrreq) {
        struct mbuf *m = m_get(M_WAIT, MT_SONAME);
        if (m) {
            *(struct socket **)m->m_data = so2;
            m->m_len = sizeof(struct socket *);
            error = so1->so_proto->pr_usrreq(so1, PRU_CONNECT2, NULL, m, NULL);
            m_free(m);
        }
    }

    if (error) {
        soclose(so1);
        soclose(so2);
        return -error;
    }

    /* Mark as connected */
    atomic_fetch_or(&so1->so_state, SS_ISCONNECTED);
    atomic_fetch_or(&so2->so_state, SS_ISCONNECTED);

    /* Apply flags */
    if (flags & SOCK_NONBLOCK) {
        so1->so_state |= SS_NBIO;
        so2->so_state |= SS_NBIO;
    }

    sv[0] = socket_alloc_fd(so1);
    sv[1] = socket_alloc_fd(so2);

    if (sv[0] < 0 || sv[1] < 0) {
        if (sv[0] >= 0) socket_free_fd(sv[0]);
        if (sv[1] >= 0) socket_free_fd(sv[1]);
        soclose(so1);
        soclose(so2);
        return -EMFILE;
    }

    return 0;
}

/*
 * POSIX bind(2)
 */
int
sys_bind(int fd, const struct sockaddr *addr, socklen_t addrlen)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    return -sobind(so, (struct sockaddr *)addr, addrlen);
}

/*
 * POSIX listen(2)
 */
int
sys_listen(int fd, int backlog)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    return -solisten(so, backlog);
}

/*
 * POSIX accept(2)
 */
int
sys_accept(int fd, struct sockaddr *addr, socklen_t *addrlen)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    if ((so->so_options & SO_ACCEPTCONN) == 0)
        return -EINVAL;

    /* Wait for connection */
    while (so->so_qlen == 0) {
        if (so->so_state & SS_NBIO)
            return -EWOULDBLOCK;
        /* Would block here in full implementation */
        return -EWOULDBLOCK;
    }

    /* Dequeue connection */
    struct socket *newso = so->so_q;
    if (newso == NULL)
        return -ECONNABORTED;

    so->so_q = newso->so_q;
    so->so_qlen--;
    newso->so_head = NULL;

    /* Get peer address */
    if (addr && addrlen) {
        if (newso->so_proto->pr_peeraddr) {
            newso->so_proto->pr_peeraddr(newso, addr);
            *addrlen = sizeof(struct sockaddr_storage);
        }
    }

    int newfd = socket_alloc_fd(newso);
    if (newfd < 0) {
        soclose(newso);
        return -EMFILE;
    }

    return newfd;
}

/*
 * POSIX accept4(2) - Linux extension
 */
int
sys_accept4(int fd, struct sockaddr *addr, socklen_t *addrlen, int flags)
{
    int newfd = sys_accept(fd, addr, addrlen);
    if (newfd < 0)
        return newfd;

    struct socket *so = socket_from_fd(newfd);
    if (so) {
        if (flags & SOCK_NONBLOCK)
            so->so_state |= SS_NBIO;
        socket_table[newfd].flags = flags;
    }

    return newfd;
}

/*
 * POSIX connect(2)
 */
int
sys_connect(int fd, const struct sockaddr *addr, socklen_t addrlen)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    int error = soconnect(so, (struct sockaddr *)addr, addrlen);
    if (error)
        return -error;

    /* Wait for connection to complete (for SOCK_STREAM) */
    if (so->so_type == SOCK_STREAM) {
        while ((atomic_load(&so->so_state) & SS_ISCONNECTING) &&
               (atomic_load(&so->so_error) == 0)) {
            if (so->so_state & SS_NBIO)
                return -EINPROGRESS;
            /* Would block here */
            return -EINPROGRESS;
        }
        error = atomic_load(&so->so_error);
        if (error) {
            atomic_store(&so->so_error, 0);
            return -error;
        }
    }

    return 0;
}

/*
 * POSIX shutdown(2)
 */
int
sys_shutdown(int fd, int how)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    switch (how) {
    case SHUT_RD:
        atomic_fetch_or(&so->so_state, SS_CANTRCVMORE);
        sorwakeup(so);
        break;
    case SHUT_WR:
        atomic_fetch_or(&so->so_state, SS_CANTSENDMORE);
        if (so->so_proto->pr_shutdown)
            so->so_proto->pr_shutdown(so);
        sowwakeup(so);
        break;
    case SHUT_RDWR:
        atomic_fetch_or(&so->so_state, SS_CANTRCVMORE | SS_CANTSENDMORE);
        if (so->so_proto->pr_shutdown)
            so->so_proto->pr_shutdown(so);
        sorwakeup(so);
        sowwakeup(so);
        break;
    default:
        return -EINVAL;
    }

    return 0;
}

/*
 * POSIX send(2)
 */
ssize_t
sys_send(int fd, const void *buf, size_t len, int flags)
{
    return sys_sendto(fd, buf, len, flags, NULL, 0);
}

/*
 * POSIX sendto(2)
 */
ssize_t
sys_sendto(int fd, const void *buf, size_t len, int flags,
           const struct sockaddr *dest_addr, socklen_t addrlen)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    /* Check if we can send */
    if (atomic_load(&so->so_state) & SS_CANTSENDMORE)
        return -EPIPE;

    /* Build uio */
    struct iovec iov = { .iov_base = (void *)buf, .iov_len = len };
    uio_t uio = {
        .uio_iov = &iov,
        .uio_iovcnt = 1,
        .uio_resid = len
    };

    int error = sosend(so, (struct sockaddr *)dest_addr, &uio, NULL, NULL, flags);
    if (error)
        return -error;

    return len - uio.uio_resid;
}

/*
 * POSIX sendmsg(2)
 */
ssize_t
sys_sendmsg(int fd, const struct msghdr *msg, int flags)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    if (atomic_load(&so->so_state) & SS_CANTSENDMORE)
        return -EPIPE;

    /* Calculate total length */
    size_t total = 0;
    for (size_t i = 0; i < msg->msg_iovlen; i++)
        total += msg->msg_iov[i].iov_len;

    uio_t uio = {
        .uio_iov = msg->msg_iov,
        .uio_iovcnt = msg->msg_iovlen,
        .uio_resid = total
    };

    /* Handle control messages */
    struct mbuf *control = NULL;
    if (msg->msg_control && msg->msg_controllen > 0) {
        control = m_get(M_WAIT, MT_CONTROL);
        if (control) {
            memcpy(control->m_data, msg->msg_control, msg->msg_controllen);
            control->m_len = msg->msg_controllen;
        }
    }

    int error = sosend(so, msg->msg_name, &uio, NULL, control, flags);
    if (error)
        return -error;

    return total - uio.uio_resid;
}

/*
 * POSIX recv(2)
 */
ssize_t
sys_recv(int fd, void *buf, size_t len, int flags)
{
    return sys_recvfrom(fd, buf, len, flags, NULL, NULL);
}

/*
 * POSIX recvfrom(2)
 */
ssize_t
sys_recvfrom(int fd, void *buf, size_t len, int flags,
             struct sockaddr *src_addr, socklen_t *addrlen)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    struct iovec iov = { .iov_base = buf, .iov_len = len };
    uio_t uio = {
        .uio_iov = &iov,
        .uio_iovcnt = 1,
        .uio_resid = len
    };

    struct sockaddr *addr = NULL;
    int error = soreceive(so, src_addr ? &addr : NULL, &uio, NULL, NULL, &flags);

    if (error)
        return -error;

    if (addr && src_addr && addrlen) {
        socklen_t copylen = *addrlen;
        if (copylen > sizeof(struct sockaddr_storage))
            copylen = sizeof(struct sockaddr_storage);
        memcpy(src_addr, addr, copylen);
        *addrlen = copylen;
    }

    return len - uio.uio_resid;
}

/*
 * POSIX recvmsg(2)
 */
ssize_t
sys_recvmsg(int fd, struct msghdr *msg, int flags)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    size_t total = 0;
    for (size_t i = 0; i < msg->msg_iovlen; i++)
        total += msg->msg_iov[i].iov_len;

    uio_t uio = {
        .uio_iov = msg->msg_iov,
        .uio_iovcnt = msg->msg_iovlen,
        .uio_resid = total
    };

    struct sockaddr *addr = NULL;
    struct mbuf *control = NULL;
    int error = soreceive(so, msg->msg_name ? &addr : NULL,
                          &uio, NULL, &control, &flags);

    if (error)
        return -error;

    if (addr && msg->msg_name) {
        memcpy(msg->msg_name, addr, msg->msg_namelen);
    }

    if (control && msg->msg_control) {
        size_t copylen = control->m_len;
        if (copylen > msg->msg_controllen)
            copylen = msg->msg_controllen;
        memcpy(msg->msg_control, control->m_data, copylen);
        msg->msg_controllen = copylen;
        m_free(control);
    }

    msg->msg_flags = flags;
    return total - uio.uio_resid;
}

/*
 * POSIX getsockname(2)
 */
int
sys_getsockname(int fd, struct sockaddr *addr, socklen_t *addrlen)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    if (so->so_proto->pr_sockaddr) {
        int error = so->so_proto->pr_sockaddr(so, addr);
        if (error)
            return -error;
        *addrlen = sizeof(struct sockaddr_storage);
        return 0;
    }

    return -EOPNOTSUPP;
}

/*
 * POSIX getpeername(2)
 */
int
sys_getpeername(int fd, struct sockaddr *addr, socklen_t *addrlen)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    if ((atomic_load(&so->so_state) & SS_ISCONNECTED) == 0)
        return -ENOTCONN;

    if (so->so_proto->pr_peeraddr) {
        int error = so->so_proto->pr_peeraddr(so, addr);
        if (error)
            return -error;
        *addrlen = sizeof(struct sockaddr_storage);
        return 0;
    }

    return -EOPNOTSUPP;
}

/*
 * POSIX setsockopt(2)
 */
int
sys_setsockopt(int fd, int level, int optname,
               const void *optval, socklen_t optlen)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    return -sosetopt(so, level, optname, optval, optlen);
}

/*
 * POSIX getsockopt(2)
 */
int
sys_getsockopt(int fd, int level, int optname,
               void *optval, socklen_t *optlen)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    return -sogetopt(so, level, optname, optval, optlen);
}

/*
 * Close socket (called from file close)
 */
int
sys_socket_close(int fd)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    socket_free_fd(fd);
    return -soclose(so);
}

/*
 * Socket pledge (exokernel extension)
 * Restricts socket capabilities (OpenBSD pledge-inspired)
 */
int
sys_socket_pledge(int fd, uint32_t promises)
{
    struct socket *so = socket_from_fd(fd);
    if (so == NULL)
        return -EBADF;

    return -sopledge(so, promises);
}

/* uio_t and SOCK_NONBLOCK/SOCK_CLOEXEC are defined at the top of this file */
