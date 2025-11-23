/**
 * @file bsd_socket.c
 * @brief BSD Socket Implementation for Exokernel LibOS
 *
 * Synthesized implementation from:
 * - 4.4BSD: Core socket model, sosend/soreceive
 * - FreeBSD: Zero-copy, sendfile concepts
 * - NetBSD: Clean protocol separation
 * - OpenBSD: pledge-style capability restrictions
 * - DragonFlyBSD: Lock-free atomic operations
 *
 * References:
 * - https://github.com/openbsd/src/blob/master/sys/kern/uipc_socket.c
 * - https://github.com/freebsd/freebsd-src/blob/main/sys/kern/uipc_socket.c
 * - https://www.netbsd.org/docs/internals/en/chap-networking-core.html
 */

#include "socketvar.h"
#include "protosw.h"
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <stdatomic.h>

/* Default buffer sizes */
#define SOCKET_SNDBUF_DEFAULT   (32 * 1024)
#define SOCKET_RCVBUF_DEFAULT   (32 * 1024)
#define SOCKET_MAXCONN_DEFAULT  128

/* Protocol control output codes */
#define PRCO_GETOPT     0
#define PRCO_SETOPT     1

/* Socket pool for fast allocation */
static struct socket *socket_pool = NULL;
static _Atomic(int) socket_pool_count = 0;

/* Domain list head */
static struct domain *domains = NULL;

/* Global socket promises (OpenBSD-style default) */
static uint32_t global_socket_promises = SOCK_PROMISES_ALL;

/*
 * Domain management
 */

void
domain_add(struct domain *dp)
{
    dp->dom_next = domains;
    domains = dp;

    if (dp->dom_init)
        dp->dom_init();
}

static struct domain *
domain_find(int family)
{
    struct domain *dp;
    for (dp = domains; dp != NULL; dp = dp->dom_next) {
        if (dp->dom_family == family)
            return dp;
    }
    return NULL;
}

/*
 * Protocol lookup (from 4.4BSD)
 */

struct protosw *
pffindtype(int family, int type)
{
    struct domain *dp = domain_find(family);
    if (dp == NULL)
        return NULL;

    struct protosw *pr;
    for (pr = dp->dom_protosw; pr < dp->dom_protoswend; pr++) {
        if (pr->pr_type == type)
            return pr;
    }
    return NULL;
}

struct protosw *
pffindproto(int family, int protocol, int type)
{
    struct domain *dp = domain_find(family);
    if (dp == NULL)
        return NULL;

    struct protosw *pr, *maybe = NULL;
    for (pr = dp->dom_protosw; pr < dp->dom_protoswend; pr++) {
        if (pr->pr_protocol == protocol && pr->pr_type == type)
            return pr;
        if (type == SOCK_RAW && pr->pr_type == SOCK_RAW &&
            pr->pr_protocol == 0 && maybe == NULL)
            maybe = pr;
    }
    return maybe;
}

/*
 * Socket buffer operations
 */

void
sbinit(struct sockbuf *sb, uint32_t hiwat)
{
    memset(sb, 0, sizeof(*sb));
    sb->sb_hiwat = hiwat;
    sb->sb_mbmax = hiwat * 2;   /* Allow some overhead for headers */
    sb->sb_lowat = 1;           /* Wake on any data */
}

void
sbrelease(struct sockbuf *sb)
{
    /* Free all mbufs in the buffer */
    if (sb->sb_mb) {
        m_freem(sb->sb_mb);
        sb->sb_mb = NULL;
        sb->sb_mbtail = NULL;
    }
    atomic_store(&sb->sb_cc, 0);
    atomic_store(&sb->sb_mbcnt, 0);
}

int
sbappend(struct sockbuf *sb, struct mbuf *m)
{
    if (m == NULL)
        return 0;

    /* Calculate total length */
    uint32_t len = 0;
    for (struct mbuf *n = m; n != NULL; n = n->m_next)
        len += n->m_len;

    /* Check space */
    if (atomic_load(&sb->sb_cc) + len > sb->sb_hiwat)
        return ENOBUFS;

    /* Append to chain */
    if (sb->sb_mbtail == NULL) {
        sb->sb_mb = m;
    } else {
        sb->sb_mbtail->m_next = m;
    }

    /* Find new tail */
    while (m->m_next != NULL)
        m = m->m_next;
    sb->sb_mbtail = m;

    atomic_fetch_add(&sb->sb_cc, len);
    return 0;
}

void
sbflush(struct sockbuf *sb)
{
    sbrelease(sb);
    sbinit(sb, sb->sb_hiwat);
}

void
sbdrop(struct sockbuf *sb, int len)
{
    struct mbuf *m = sb->sb_mb;

    while (len > 0 && m != NULL) {
        if (m->m_len <= (uint32_t)len) {
            len -= m->m_len;
            atomic_fetch_sub(&sb->sb_cc, m->m_len);
            struct mbuf *n = m->m_next;
            m_free(m);
            m = n;
        } else {
            m->m_data += len;
            m->m_len -= len;
            atomic_fetch_sub(&sb->sb_cc, len);
            len = 0;
        }
    }
    sb->sb_mb = m;
    if (m == NULL)
        sb->sb_mbtail = NULL;
}

/*
 * mbuf operations (simplified)
 */

struct mbuf *
m_get(int how, int type)
{
    struct mbuf *m = malloc(sizeof(struct mbuf));
    if (m == NULL && how == M_WAIT) {
        /* In a real implementation, would wait for memory */
        return NULL;
    }
    if (m == NULL)
        return NULL;

    memset(m, 0, sizeof(*m));
    m->m_type = type;
    m->m_data = m->m_dat.m_dat;
    return m;
}

struct mbuf *
m_gethdr(int how, int type)
{
    struct mbuf *m = m_get(how, type);
    if (m != NULL) {
        m->m_flags |= M_PKTHDR;
        m->m_data = m->m_dat.m_dat + sizeof(m->m_dat.m_pkthdr);
    }
    return m;
}

void
m_free(struct mbuf *m)
{
    if (m != NULL) {
        if (m->m_flags & M_EXT) {
            /* Free external storage */
            /* In full implementation, would free cluster */
        }
        free(m);
    }
}

void
m_freem(struct mbuf *m)
{
    while (m != NULL) {
        struct mbuf *n = m->m_next;
        m_free(m);
        m = n;
    }
}

struct mbuf *
m_copym(struct mbuf *m, int off, int len, int how)
{
    struct mbuf *top = NULL, *tail = NULL;

    /* Skip offset */
    while (off > 0 && m != NULL) {
        if (off < (int)m->m_len)
            break;
        off -= m->m_len;
        m = m->m_next;
    }

    /* Copy data */
    while (len > 0 && m != NULL) {
        struct mbuf *n = m_get(how, m->m_type);
        if (n == NULL) {
            m_freem(top);
            return NULL;
        }

        int tocopy = m->m_len - off;
        if (tocopy > len)
            tocopy = len;
        if (tocopy > MLEN)
            tocopy = MLEN;

        memcpy(n->m_data, m->m_data + off, tocopy);
        n->m_len = tocopy;
        len -= tocopy;
        off = 0;

        if (top == NULL) {
            top = n;
        } else {
            tail->m_next = n;
        }
        tail = n;
        m = m->m_next;
    }

    return top;
}

void
m_adj(struct mbuf *m, int len)
{
    if (len >= 0) {
        /* Trim from head */
        while (m != NULL && len > 0) {
            if (m->m_len <= (uint32_t)len) {
                len -= m->m_len;
                m->m_len = 0;
                m = m->m_next;
            } else {
                m->m_len -= len;
                m->m_data += len;
                len = 0;
            }
        }
    } else {
        /* Trim from tail - find end first */
        len = -len;
        struct mbuf *n = m;
        uint32_t total = 0;
        while (n != NULL) {
            total += n->m_len;
            n = n->m_next;
        }
        if ((uint32_t)len > total)
            len = total;
        total -= len;

        /* Now trim to 'total' bytes */
        n = m;
        while (n != NULL && total > 0) {
            if (n->m_len <= total) {
                total -= n->m_len;
                n = n->m_next;
            } else {
                n->m_len = total;
                total = 0;
                /* Free remaining */
                m_freem(n->m_next);
                n->m_next = NULL;
            }
        }
    }
}

/*
 * Socket creation (from 4.4BSD socreate)
 */

int
socreate(int domain, struct socket **aso, int type, int protocol)
{
    struct socket *so;
    struct protosw *pr;
    int error;

    /* Find protocol */
    if (protocol)
        pr = pffindproto(domain, protocol, type);
    else
        pr = pffindtype(domain, type);

    if (pr == NULL)
        return EPROTONOSUPPORT;

    if (pr->pr_type != type)
        return EPROTOTYPE;

    /* Allocate socket */
    so = malloc(sizeof(struct socket));
    if (so == NULL)
        return ENOMEM;
    memset(so, 0, sizeof(*so));

    so->so_type = type;
    so->so_proto = pr;
    atomic_store(&so->so_refs, 1);
    so->so_promises = global_socket_promises;

    /* Initialize buffers */
    sbinit(&so->so_snd, SOCKET_SNDBUF_DEFAULT);
    sbinit(&so->so_rcv, SOCKET_RCVBUF_DEFAULT);

    /* Protocol attach */
    if (pr->pr_attach) {
        error = pr->pr_attach(so, protocol);
    } else if (pr->pr_usrreq) {
        error = pr->pr_usrreq(so, PRU_ATTACH, NULL, NULL, NULL);
    } else {
        error = ENOPROTOOPT;
    }

    if (error) {
        free(so);
        return error;
    }

    *aso = so;
    return 0;
}

/*
 * Socket binding
 */

int
sobind(struct socket *so, struct sockaddr *nam, size_t namlen)
{
    int error;

    /* Check pledge promise */
    if ((error = socheck_promise(so, SOCK_PROMISE_BIND)) != 0)
        return error;

    if (so->so_proto->pr_bind) {
        error = so->so_proto->pr_bind(so, nam, namlen);
    } else if (so->so_proto->pr_usrreq) {
        struct mbuf *m = m_get(M_WAIT, MT_SONAME);
        if (m == NULL)
            return ENOBUFS;
        m->m_len = namlen;
        memcpy(m->m_data, nam, namlen);
        error = so->so_proto->pr_usrreq(so, PRU_BIND, NULL, m, NULL);
        m_free(m);
    } else {
        error = EOPNOTSUPP;
    }

    return error;
}

/*
 * Socket listen
 */

int
solisten(struct socket *so, int backlog)
{
    int error;

    /* Check pledge promise */
    if ((error = socheck_promise(so, SOCK_PROMISE_LISTEN)) != 0)
        return error;

    if (backlog < 0 || backlog > SOCKET_MAXCONN_DEFAULT)
        backlog = SOCKET_MAXCONN_DEFAULT;

    if (so->so_proto->pr_listen) {
        error = so->so_proto->pr_listen(so, backlog);
    } else if (so->so_proto->pr_usrreq) {
        error = so->so_proto->pr_usrreq(so, PRU_LISTEN, NULL, NULL, NULL);
    } else {
        error = EOPNOTSUPP;
    }

    if (error == 0) {
        so->so_qlimit = backlog;
        so->so_options |= SO_ACCEPTCONN;
    }

    return error;
}

/*
 * Socket connect
 */

int
soconnect(struct socket *so, struct sockaddr *nam, size_t namlen)
{
    int error;

    /* Check pledge promise */
    if ((error = socheck_promise(so, SOCK_PROMISE_CONNECT)) != 0)
        return error;

    if (atomic_load(&so->so_state) & (SS_ISCONNECTED | SS_ISCONNECTING))
        return EISCONN;

    if (so->so_proto->pr_connect) {
        error = so->so_proto->pr_connect(so, nam, namlen);
    } else if (so->so_proto->pr_usrreq) {
        struct mbuf *m = m_get(M_WAIT, MT_SONAME);
        if (m == NULL)
            return ENOBUFS;
        m->m_len = namlen;
        memcpy(m->m_data, nam, namlen);
        error = so->so_proto->pr_usrreq(so, PRU_CONNECT, NULL, m, NULL);
        m_free(m);
    } else {
        error = EOPNOTSUPP;
    }

    return error;
}

/*
 * Socket accept
 */

int
soaccept(struct socket *so, struct sockaddr *nam)
{
    int error = 0;

    if ((so->so_options & SO_ACCEPTCONN) == 0)
        return EINVAL;

    if (so->so_proto->pr_accept) {
        error = so->so_proto->pr_accept(so, nam);
    } else if (so->so_proto->pr_usrreq) {
        struct mbuf *m = m_get(M_WAIT, MT_SONAME);
        if (m == NULL)
            return ENOBUFS;
        error = so->so_proto->pr_usrreq(so, PRU_ACCEPT, NULL, m, NULL);
        if (error == 0 && nam != NULL)
            memcpy(nam, m->m_data, m->m_len);
        m_free(m);
    }

    return error;
}

/*
 * Socket disconnect
 */

int
sodisconnect(struct socket *so)
{
    int error;

    if ((atomic_load(&so->so_state) & SS_ISCONNECTED) == 0)
        return ENOTCONN;

    if (so->so_proto->pr_disconnect) {
        error = so->so_proto->pr_disconnect(so);
    } else if (so->so_proto->pr_usrreq) {
        error = so->so_proto->pr_usrreq(so, PRU_DISCONNECT, NULL, NULL, NULL);
    } else {
        error = EOPNOTSUPP;
    }

    return error;
}

/*
 * Socket close
 */

int
soclose(struct socket *so)
{
    int error = 0;

    /* Drop reference */
    if (atomic_fetch_sub(&so->so_refs, 1) > 1)
        return 0;

    /* Disconnect if connected */
    if (atomic_load(&so->so_state) & SS_ISCONNECTED) {
        error = sodisconnect(so);
    }

    /* Handle linger */
    if (so->so_options & SO_LINGER) {
        int16_t linger = atomic_load(&so->so_linger);
        if (linger > 0) {
            /* Would sleep here in full implementation */
        }
    }

    /* Protocol detach */
    if (so->so_proto->pr_detach) {
        so->so_proto->pr_detach(so);
    } else if (so->so_proto->pr_usrreq) {
        so->so_proto->pr_usrreq(so, PRU_DETACH, NULL, NULL, NULL);
    }

    /* Release buffers */
    sbrelease(&so->so_snd);
    sbrelease(&so->so_rcv);

    /* Free socket */
    free(so);

    return error;
}

/*
 * Socket abort (for error cases)
 */

int
soabort(struct socket *so)
{
    if (so->so_proto->pr_usrreq) {
        so->so_proto->pr_usrreq(so, PRU_ABORT, NULL, NULL, NULL);
    }
    return soclose(so);
}

/*
 * sosend - send data on socket (from 4.4BSD)
 * This is the main data transmission path
 */

int
sosend(struct socket *so, struct sockaddr *addr,
       uio_t *uio, struct mbuf *top,
       struct mbuf *control, int flags)
{
    struct mbuf *m = NULL;
    long space;
    int error = 0;
    int dontroute = (flags & MSG_DONTROUTE) &&
                    (so->so_options & SO_DONTROUTE) == 0;

    if (uio != NULL)
        top = NULL;     /* uio takes precedence */

    /* Check connection state for stream sockets */
    if (so->so_type == SOCK_STREAM) {
        int16_t state = atomic_load(&so->so_state);
        if ((state & SS_ISCONNECTED) == 0) {
            if (addr == NULL)
                return ENOTCONN;
            if ((state & SS_ISCONNECTING) == 0)
                return ENOTCONN;
        }
    }

    /* Check for space in send buffer */
    space = so->so_snd.sb_hiwat - atomic_load(&so->so_snd.sb_cc);
    if (space < 0)
        space = 0;

    /* For now, simple implementation - copy data to mbuf */
    if (uio != NULL && uio->uio_resid > 0) {
        /* Would implement scatter/gather I/O here */
        /* For now, just allocate single mbuf */
        size_t len = uio->uio_resid;
        if (len > (size_t)space)
            len = space;

        m = m_get(M_WAIT, MT_DATA);
        if (m == NULL)
            return ENOBUFS;

        /* Copy from uio (simplified) */
        if (uio->uio_iov && uio->uio_iovcnt > 0) {
            size_t tocopy = len < MLEN ? len : MLEN;
            memcpy(m->m_data, uio->uio_iov[0].iov_base, tocopy);
            m->m_len = tocopy;
        }
        top = m;
    }

    /* Send via protocol */
    if (dontroute)
        so->so_options |= SO_DONTROUTE;

    if (so->so_proto->pr_send) {
        error = so->so_proto->pr_send(so, top, addr, control);
    } else if (so->so_proto->pr_usrreq) {
        struct mbuf *nam = NULL;
        if (addr) {
            nam = m_get(M_WAIT, MT_SONAME);
            if (nam) {
                memcpy(nam->m_data, addr, sizeof(struct sockaddr_storage));
                nam->m_len = sizeof(struct sockaddr_storage);
            }
        }
        error = so->so_proto->pr_usrreq(so, PRU_SEND, top, nam, control);
        if (nam)
            m_free(nam);
    } else {
        error = EOPNOTSUPP;
        m_freem(top);
    }

    if (dontroute)
        so->so_options &= ~SO_DONTROUTE;

    return error;
}

/*
 * soreceive - receive data from socket (from 4.4BSD)
 * This is the main data reception path
 */

int
soreceive(struct socket *so, struct sockaddr **paddr,
          uio_t *uio, struct mbuf **mp0,
          struct mbuf **controlp, int *flagsp)
{
    struct mbuf *m;
    int flags = flagsp ? *flagsp : 0;
    int error = 0;
    size_t len;

    if (paddr)
        *paddr = NULL;
    if (controlp)
        *controlp = NULL;
    if (mp0)
        *mp0 = NULL;

    /* Check for data in receive buffer */
    if (atomic_load(&so->so_rcv.sb_cc) == 0) {
        if (atomic_load(&so->so_state) & SS_CANTRCVMORE)
            return 0;   /* EOF */
        if ((flags & MSG_DONTWAIT) || (so->so_state & SS_NBIO))
            return EWOULDBLOCK;
        /* Would block and wait here in full implementation */
        return EWOULDBLOCK;
    }

    /* Get data from buffer */
    m = so->so_rcv.sb_mb;
    if (m == NULL)
        return 0;

    /* Copy to uio or return mbuf */
    if (mp0) {
        /* Return mbuf directly (zero-copy path) */
        *mp0 = m;
        so->so_rcv.sb_mb = NULL;
        so->so_rcv.sb_mbtail = NULL;
        atomic_store(&so->so_rcv.sb_cc, 0);
    } else if (uio) {
        /* Copy to user buffer */
        len = uio->uio_resid;
        if (len > atomic_load(&so->so_rcv.sb_cc))
            len = atomic_load(&so->so_rcv.sb_cc);

        /* Simple copy - would handle scatter/gather in full impl */
        if (uio->uio_iov && uio->uio_iovcnt > 0 && m) {
            size_t tocopy = len < m->m_len ? len : m->m_len;
            memcpy(uio->uio_iov[0].iov_base, m->m_data, tocopy);
            uio->uio_resid -= tocopy;

            if (!(flags & MSG_PEEK))
                sbdrop(&so->so_rcv, tocopy);
        }
    }

    return error;
}

/*
 * Socket wakeup functions
 */

void
sowakeup(struct socket *so, struct sockbuf *sb)
{
    uint32_t flags = atomic_load(&sb->sb_flags);

    if (flags & SB_WAIT) {
        atomic_fetch_and(&sb->sb_flags, ~SB_WAIT);
        /* Would wakeup sleeping threads here */
    }
    if (flags & SB_SEL) {
        /* Would notify select/poll here */
    }
    if (flags & SB_ASYNC) {
        /* Would send SIGIO here */
    }
    if (flags & SB_KNOTE) {
        /* Would trigger kqueue here */
    }
}

void
sorwakeup(struct socket *so)
{
    sowakeup(so, &so->so_rcv);
}

void
sowwakeup(struct socket *so)
{
    sowakeup(so, &so->so_snd);
}

/*
 * Socket options
 */

int
sosetopt(struct socket *so, int level, int optname,
         const void *optval, socklen_t optlen)
{
    int error = 0;

    if (level != SOL_SOCKET) {
        /* Delegate to protocol */
        if (so->so_proto->pr_ctloutput) {
            struct mbuf *m = NULL;
            if (optval && optlen > 0) {
                m = m_get(M_WAIT, MT_DATA);
                if (m) {
                    memcpy(m->m_data, optval, optlen);
                    m->m_len = optlen;
                }
            }
            error = so->so_proto->pr_ctloutput(PRCO_SETOPT, so,
                                                level, optname, &m);
            if (m)
                m_free(m);
        } else {
            error = ENOPROTOOPT;
        }
        return error;
    }

    /* Socket-level options */
    switch (optname) {
    case SO_LINGER:
        if (optlen >= sizeof(struct linger)) {
            const struct linger *l = optval;
            if (l->l_onoff)
                so->so_options |= SO_LINGER;
            else
                so->so_options &= ~SO_LINGER;
            atomic_store(&so->so_linger, l->l_linger);
        }
        break;

    case SO_DEBUG:
    case SO_KEEPALIVE:
    case SO_DONTROUTE:
    case SO_BROADCAST:
    case SO_REUSEADDR:
    case SO_REUSEPORT:
    case SO_OOBINLINE:
        if (optval && *(const int *)optval)
            so->so_options |= optname;
        else
            so->so_options &= ~optname;
        break;

    case SO_SNDBUF:
        if (optlen >= sizeof(int)) {
            so->so_snd.sb_hiwat = *(const int *)optval;
        }
        break;

    case SO_RCVBUF:
        if (optlen >= sizeof(int)) {
            so->so_rcv.sb_hiwat = *(const int *)optval;
        }
        break;

    case SO_SNDLOWAT:
        if (optlen >= sizeof(int)) {
            so->so_snd.sb_lowat = *(const int *)optval;
        }
        break;

    case SO_RCVLOWAT:
        if (optlen >= sizeof(int)) {
            so->so_rcv.sb_lowat = *(const int *)optval;
        }
        break;

    default:
        error = ENOPROTOOPT;
        break;
    }

    return error;
}

int
sogetopt(struct socket *so, int level, int optname,
         void *optval, socklen_t *optlen)
{
    int error = 0;

    if (level != SOL_SOCKET) {
        /* Delegate to protocol */
        if (so->so_proto->pr_ctloutput) {
            struct mbuf *m = NULL;
            error = so->so_proto->pr_ctloutput(PRCO_GETOPT, so,
                                                level, optname, &m);
            if (error == 0 && m) {
                size_t len = m->m_len < *optlen ? m->m_len : *optlen;
                memcpy(optval, m->m_data, len);
                *optlen = len;
                m_free(m);
            }
        } else {
            error = ENOPROTOOPT;
        }
        return error;
    }

    /* Socket-level options */
    switch (optname) {
    case SO_LINGER:
        if (*optlen >= sizeof(struct linger)) {
            struct linger *l = optval;
            l->l_onoff = (so->so_options & SO_LINGER) ? 1 : 0;
            l->l_linger = atomic_load(&so->so_linger);
            *optlen = sizeof(struct linger);
        }
        break;

    case SO_ERROR:
        *(int *)optval = atomic_exchange(&so->so_error, 0);
        *optlen = sizeof(int);
        break;

    case SO_TYPE:
        *(int *)optval = so->so_type;
        *optlen = sizeof(int);
        break;

    case SO_DEBUG:
    case SO_KEEPALIVE:
    case SO_DONTROUTE:
    case SO_BROADCAST:
    case SO_REUSEADDR:
    case SO_REUSEPORT:
    case SO_OOBINLINE:
    case SO_ACCEPTCONN:
        *(int *)optval = (so->so_options & optname) ? 1 : 0;
        *optlen = sizeof(int);
        break;

    case SO_SNDBUF:
        *(int *)optval = so->so_snd.sb_hiwat;
        *optlen = sizeof(int);
        break;

    case SO_RCVBUF:
        *(int *)optval = so->so_rcv.sb_hiwat;
        *optlen = sizeof(int);
        break;

    default:
        error = ENOPROTOOPT;
        break;
    }

    return error;
}

/*
 * Exokernel capability integration (OpenBSD pledge-inspired)
 */

int
sopledge(struct socket *so, uint32_t promises)
{
    /* Can only reduce promises, never increase */
    so->so_promises &= promises;
    atomic_fetch_or(&so->so_state, SS_PLEDGED);
    return 0;
}

int
socheck_promise(struct socket *so, uint32_t promise)
{
    if (atomic_load(&so->so_state) & SS_PLEDGED) {
        if ((so->so_promises & promise) == 0)
            return EPERM;   /* Would be SIGABRT in OpenBSD */
    }
    return 0;
}

int
socap_attach(struct socket *so, void *cap)
{
    so->so_cap = cap;
    atomic_fetch_or(&so->so_state, SS_CAPMODE);
    return 0;
}

/*
 * Socket state transitions (used by protocol handlers)
 */

void
soisconnected(struct socket *so)
{
    struct socket *head = so->so_head;

    atomic_fetch_and(&so->so_state, ~(SS_ISCONNECTING | SS_ISDISCONNECTING));
    atomic_fetch_or(&so->so_state, SS_ISCONNECTED);

    if (head && head->so_qlen < head->so_qlimit) {
        /* Move from incomplete to complete queue */
        /* (Queue management simplified for this implementation) */
        sorwakeup(head);
    }

    sorwakeup(so);
    sowwakeup(so);
}

void
soisconnecting(struct socket *so)
{
    atomic_fetch_and(&so->so_state, ~(SS_ISCONNECTED | SS_ISDISCONNECTING));
    atomic_fetch_or(&so->so_state, SS_ISCONNECTING);
}

void
soisdisconnected(struct socket *so)
{
    atomic_fetch_and(&so->so_state,
        ~(SS_ISCONNECTING | SS_ISCONNECTED | SS_ISDISCONNECTING));
    atomic_fetch_or(&so->so_state, SS_ISDISCONNECTED | SS_CANTRCVMORE | SS_CANTSENDMORE);
    sorwakeup(so);
    sowwakeup(so);
}

void
soisdisconnecting(struct socket *so)
{
    atomic_fetch_and(&so->so_state, ~SS_ISCONNECTING);
    atomic_fetch_or(&so->so_state, SS_ISDISCONNECTING | SS_CANTRCVMORE | SS_CANTSENDMORE);
    sorwakeup(so);
    sowwakeup(so);
}

void
socantsendmore(struct socket *so)
{
    atomic_fetch_or(&so->so_state, SS_CANTSENDMORE);
    sowwakeup(so);
}

void
socantrcvmore(struct socket *so)
{
    atomic_fetch_or(&so->so_state, SS_CANTRCVMORE);
    sorwakeup(so);
}

/*
 * Additional socket buffer operations
 */

int
sbappendcontrol(struct sockbuf *sb, struct mbuf *m0, struct mbuf *control)
{
    /* Append control message to buffer */
    if (control == NULL)
        return sbappend(sb, m0);

    /* Chain control after data */
    if (m0) {
        struct mbuf *m = m0;
        while (m->m_next)
            m = m->m_next;
        m->m_next = control;
        return sbappend(sb, m0);
    }

    return sbappend(sb, control);
}

int
sbreserve(struct sockbuf *sb, uint32_t cc)
{
    sb->sb_hiwat = cc;
    sb->sb_mbmax = cc * 2;  /* Allow some overhead for mbuf headers */
    return 0;
}

void
sbwait(struct sockbuf *sb)
{
    atomic_fetch_or(&sb->sb_flags, SB_WAIT);
    /* Would sleep here in full implementation */
}

void
sbwakeup(struct sockbuf *sb)
{
    uint32_t flags = atomic_load(&sb->sb_flags);
    if (flags & SB_WAIT) {
        atomic_fetch_and(&sb->sb_flags, ~SB_WAIT);
        /* Would wakeup sleeping threads here */
    }
}
