/**
 * @file socketvar.h
 * @brief BSD Socket Internal Structures
 *
 * Synthesized from 4.4BSD, NetBSD, FreeBSD, OpenBSD, and DragonFlyBSD.
 * This file defines the kernel-internal socket structures for the
 * exokernel libOS networking stack.
 *
 * Design Principles:
 * - 4.4BSD: Core socket/protosw model
 * - FreeBSD: Zero-copy sendfile, sf_buf concepts
 * - NetBSD: Clean protocol separation
 * - OpenBSD: Capability-based restrictions (pledge-inspired)
 * - DragonFlyBSD: Lock-free, per-CPU token model
 *
 * @see "TCP/IP Illustrated, Vol 2" for BSD networking internals
 * @see https://www.netbsd.org/docs/internals/en/chap-networking-core.html
 */

#ifndef _LIBOS_SOCKETVAR_H_
#define _LIBOS_SOCKETVAR_H_

#include <stdint.h>
#include <stddef.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <sys/socket.h>
#include <sys/uio.h>

/* Forward declarations */
struct socket;
struct sockbuf;
struct protosw;
struct mbuf;
struct exo_cap;

/*
 * User I/O structure - use system definition from sys/uio.h
 * On macOS/BSD: struct uio is kernel-internal, use iovec directly
 * For portability, we define a compatible structure only when needed
 */
#ifdef __APPLE__
/* macOS has a different internal uio structure - use a portable wrapper */
struct exo_uio {
    struct iovec   *uio_iov;        /* Scatter/gather list */
    int             uio_iovcnt;     /* Number of iovecs */
    off_t           uio_offset;     /* Offset in file/device */
    ssize_t         uio_resid;      /* Remaining bytes */
    int             uio_rw;         /* Read (0) or write (1) */
};
#define EXO_UIO_READ  0
#define EXO_UIO_WRITE 1
typedef struct exo_uio uio_t;
#else
/* Use BSD-compatible uio structure */
struct uio {
    struct iovec   *uio_iov;
    int             uio_iovcnt;
    off_t           uio_offset;
    ssize_t         uio_resid;
    int             uio_rw;
};
typedef struct uio uio_t;
#define EXO_UIO_READ  0
#define EXO_UIO_WRITE 1
#endif

/*
 * Socket buffer structure (from 4.4BSD)
 * Each socket has two buffers: send (so_snd) and receive (so_rcv)
 */
struct sockbuf {
    _Atomic(uint32_t) sb_flags;     /* Buffer flags (atomic for DragonFly-style) */
    uint32_t    sb_hiwat;           /* High water mark */
    uint32_t    sb_lowat;           /* Low water mark */
    uint32_t    sb_mbmax;           /* Max mbufs in buffer */

    _Atomic(uint32_t) sb_cc;        /* Actual chars in buffer */
    _Atomic(uint32_t) sb_mbcnt;     /* Chars of mbufs used */

    struct mbuf *sb_mb;             /* First mbuf in chain */
    struct mbuf *sb_mbtail;         /* Last mbuf in chain */
    struct mbuf *sb_lastrecord;     /* Last record marker */

    /* Async notification (kqueue-style) */
    void       *sb_sel;             /* Select/poll wakeup info */
    int         sb_timeo;           /* Timeout for I/O */

    /* Zero-copy support (FreeBSD sendfile-inspired) */
    void       *sb_zcbuf;           /* Zero-copy buffer */
    size_t      sb_zccnt;           /* Zero-copy byte count */
};

/* Socket buffer flags (sb_flags) */
#define SB_LOCK         0x0001      /* Lock on data queue */
#define SB_WANT         0x0002      /* Waiting to lock */
#define SB_WAIT         0x0004      /* Waiting for data/space */
#define SB_SEL          0x0008      /* Select pending */
#define SB_ASYNC        0x0010      /* Async I/O */
#define SB_NOINTR       0x0040      /* Operations non-interruptible */
#define SB_KNOTE        0x0100      /* kqueue note pending */
#define SB_AUTOSIZE     0x0800      /* Auto-size buffer */
#define SB_STOP         0x1000      /* Stop sending (flow control) */

/*
 * Socket state flags (from 4.4BSD so_state)
 */
#define SS_NOFDREF          0x0001  /* No file table ref */
#define SS_ISCONNECTED      0x0002  /* Socket connected */
#define SS_ISCONNECTING     0x0004  /* In process of connecting */
#define SS_ISDISCONNECTING  0x0008  /* In process of disconnecting */
#define SS_CANTSENDMORE     0x0010  /* Can't send more data */
#define SS_CANTRCVMORE      0x0020  /* Can't receive more */
#define SS_RCVATMARK        0x0040  /* At OOB mark */
#define SS_NBIO             0x0080  /* Non-blocking I/O */
#define SS_ASYNC            0x0100  /* Async I/O notify */
#define SS_ISCONFIRMING     0x0200  /* Accepting connections */
#define SS_ISDISCONNECTED   0x0400  /* Socket disconnected */
#define SS_DNS              0x0800  /* DNS-only socket (OpenBSD) */
#define SS_PLEDGED          0x1000  /* Socket under pledge */
#define SS_CAPMODE          0x2000  /* Capability mode (exokernel) */

/*
 * Socket options (from 4.4BSD so_options)
 * Guard with #ifndef to avoid conflicts with system headers
 */
#ifndef SO_DEBUG
#define SO_DEBUG        0x0001      /* Debugging info recording */
#endif
#ifndef SO_ACCEPTCONN
#define SO_ACCEPTCONN   0x0002      /* Socket has listen() */
#endif
#ifndef SO_REUSEADDR
#define SO_REUSEADDR    0x0004      /* Allow local address reuse */
#endif
#ifndef SO_KEEPALIVE
#define SO_KEEPALIVE    0x0008      /* Keep connections alive */
#endif
#ifndef SO_DONTROUTE
#define SO_DONTROUTE    0x0010      /* Just use interface addr */
#endif
#ifndef SO_BROADCAST
#define SO_BROADCAST    0x0020      /* Permit sending broadcast */
#endif
#ifndef SO_USELOOPBACK
#define SO_USELOOPBACK  0x0040      /* Bypass hardware if possible */
#endif
#ifndef SO_LINGER
#define SO_LINGER       0x0080      /* Linger on close */
#endif
#ifndef SO_OOBINLINE
#define SO_OOBINLINE    0x0100      /* Leave OOB in-line */
#endif
#ifndef SO_REUSEPORT
#define SO_REUSEPORT    0x0200      /* Allow local port reuse */
#endif
#ifndef SO_TIMESTAMP
#define SO_TIMESTAMP    0x0400      /* Timestamp received data */
#endif
#ifndef SO_NOSIGPIPE
#define SO_NOSIGPIPE    0x0800      /* No SIGPIPE on broken pipe */
#endif
#ifndef SO_ACCEPTFILTER
#define SO_ACCEPTFILTER 0x1000      /* Accept filter (FreeBSD) */
#endif
#ifndef SO_BINTIME
#define SO_BINTIME      0x2000      /* Bintime timestamp */
#endif
#ifndef SO_SETFIB
#define SO_SETFIB       0x4000      /* Set routing FIB (FreeBSD) */
#endif

/*
 * Socket capability promises (OpenBSD pledge-inspired for exokernel)
 * Integrated with PDAC capability system
 */
#define SOCK_PROMISE_INET       0x0001  /* Allow AF_INET/AF_INET6 */
#define SOCK_PROMISE_UNIX       0x0002  /* Allow AF_UNIX */
#define SOCK_PROMISE_DNS        0x0004  /* DNS resolution only */
#define SOCK_PROMISE_CONNECT    0x0008  /* Allow outbound connect */
#define SOCK_PROMISE_BIND       0x0010  /* Allow bind to port */
#define SOCK_PROMISE_LISTEN     0x0020  /* Allow listen() */
#define SOCK_PROMISE_RAW        0x0040  /* Allow raw sockets */
#define SOCK_PROMISE_MULTICAST  0x0080  /* Allow multicast */
#define SOCK_PROMISE_RECVFD     0x0100  /* Receive file descriptors */
#define SOCK_PROMISE_SENDFD     0x0200  /* Send file descriptors */
#define SOCK_PROMISE_ROUTE      0x0400  /* Routing sockets */

/* Common promise sets */
#define SOCK_PROMISES_CLIENT    (SOCK_PROMISE_INET | SOCK_PROMISE_CONNECT)
#define SOCK_PROMISES_SERVER    (SOCK_PROMISE_INET | SOCK_PROMISE_BIND | SOCK_PROMISE_LISTEN)
#define SOCK_PROMISES_LOCAL     (SOCK_PROMISE_UNIX | SOCK_PROMISE_CONNECT | SOCK_PROMISE_BIND)
#define SOCK_PROMISES_ALL       0xFFFF

/*
 * Main socket structure (4.4BSD struct socket)
 * Extended with DragonFlyBSD atomics and OpenBSD security
 */
struct socket {
    /* Protocol and type */
    int16_t         so_type;        /* SOCK_STREAM, SOCK_DGRAM, etc. */
    int16_t         so_options;     /* From socket options above */
    _Atomic(int16_t) so_linger;     /* Linger time */
    _Atomic(int16_t) so_state;      /* Internal state flags */

    /* Protocol control */
    void           *so_pcb;         /* Protocol control block */
    struct protosw *so_proto;       /* Protocol switch entry */

    /* Socket buffers */
    struct sockbuf  so_snd;         /* Send buffer */
    struct sockbuf  so_rcv;         /* Receive buffer */

    /* Connection queues (for listening sockets) */
    struct socket  *so_head;        /* Back ptr to listening socket */
    struct socket  *so_q0;          /* Incomplete connections */
    struct socket  *so_q;           /* Complete connections */
    int16_t         so_q0len;       /* Incomplete queue length */
    int16_t         so_qlen;        /* Complete queue length */
    int16_t         so_qlimit;      /* Max queued connections */
    int16_t         so_timeo;       /* Connection timeout */

    /* Error tracking */
    _Atomic(int16_t) so_error;      /* Error affecting connection */
    pid_t           so_pgid;        /* Process group for signals */
    uid_t           so_uid;         /* Owning user ID */
    gid_t           so_gid;         /* Owning group ID */

    /* Exokernel capability integration */
    uint32_t        so_promises;    /* Socket capability promises */
    void           *so_cap;         /* Exokernel capability ptr */

    /* Statistics (DragonFly-style atomics) */
    _Atomic(uint64_t) so_oobmark;   /* OOB mark */

    /* Reference counting */
    _Atomic(int32_t) so_refs;       /* Reference count */

    /* Per-CPU token (DragonFlyBSD) */
    int             so_cpu;         /* Owning CPU */
    void           *so_token;       /* Serializing token */

    /* Miscellaneous */
    uint32_t        so_fibnum;      /* Routing FIB (FreeBSD) */
    void           *so_upcall;      /* Upcall function */
    void           *so_upcallarg;   /* Upcall argument */
};

/*
 * Protocol User Request codes (from 4.4BSD PRU_*)
 * Used in protosw->pr_usrreq
 */
enum {
    PRU_ATTACH,         /* Attach protocol to socket */
    PRU_DETACH,         /* Detach protocol from socket */
    PRU_BIND,           /* Bind name to socket */
    PRU_LISTEN,         /* Listen for connections */
    PRU_CONNECT,        /* Establish connection */
    PRU_ACCEPT,         /* Accept connection */
    PRU_DISCONNECT,     /* Disconnect from peer */
    PRU_SHUTDOWN,       /* Shutdown write side */
    PRU_RCVD,           /* Have taken data */
    PRU_SEND,           /* Send data */
    PRU_ABORT,          /* Abort connection */
    PRU_CONTROL,        /* Control operations */
    PRU_SENSE,          /* Return socket status */
    PRU_RCVOOB,         /* Receive OOB data */
    PRU_SENDOOB,        /* Send OOB data */
    PRU_SOCKADDR,       /* Get local socket address */
    PRU_PEERADDR,       /* Get peer socket address */
    PRU_CONNECT2,       /* Connect two sockets */
    PRU_FASTTIMO,       /* Fast timeout (200ms) */
    PRU_SLOWTIMO,       /* Slow timeout (500ms) */
    PRU_PROTORCV,       /* Receive from below */
    PRU_PROTOSEND,      /* Send to below */
    PRU_PURGEIF,        /* Purge route for interface */
    PRU_NREQ            /* Number of requests */
};

/*
 * Protocol switch structure (from 4.4BSD struct protosw)
 * Each protocol (TCP, UDP, etc.) provides one of these
 */
struct protosw {
    int16_t     pr_type;            /* Socket type (SOCK_*) */
    int16_t     pr_protocol;        /* Protocol number */
    int16_t     pr_flags;           /* Protocol flags */
    int16_t     pr_domain;          /* Domain (AF_*) */

    /* Protocol-specific functions */
    void        (*pr_input)(struct mbuf *, int);    /* Input from below */
    int         (*pr_output)(struct mbuf *, struct socket *); /* Output to below */
    void        (*pr_ctlinput)(int, struct sockaddr *, void *); /* Control input */
    int         (*pr_ctloutput)(int, struct socket *, int, int, struct mbuf **);

    /* User request handler (main entry point) */
    int         (*pr_usrreq)(struct socket *, int, struct mbuf *,
                             struct mbuf *, struct mbuf *);

    /* New-style handlers (NetBSD/FreeBSD) */
    int         (*pr_attach)(struct socket *, int);
    int         (*pr_detach)(struct socket *);
    int         (*pr_bind)(struct socket *, struct sockaddr *, size_t);
    int         (*pr_listen)(struct socket *, int);
    int         (*pr_accept)(struct socket *, struct sockaddr *);
    int         (*pr_connect)(struct socket *, struct sockaddr *, size_t);
    int         (*pr_disconnect)(struct socket *);
    int         (*pr_shutdown)(struct socket *);
    int         (*pr_send)(struct socket *, struct mbuf *, struct sockaddr *,
                           struct mbuf *);
    int         (*pr_sendoob)(struct socket *, struct mbuf *);
    int         (*pr_rcvd)(struct socket *, int);
    int         (*pr_rcvoob)(struct socket *, struct mbuf *, int);
    int         (*pr_sockaddr)(struct socket *, struct sockaddr *);
    int         (*pr_peeraddr)(struct socket *, struct sockaddr *);

    /* Timer/slow tick */
    void        (*pr_fasttimo)(void);
    void        (*pr_slowtimo)(void);
    void        (*pr_drain)(void);

    /* Sysctl handling */
    int         (*pr_sysctl)(int *, unsigned int, void *, size_t *,
                             void *, size_t);
};

/* Protocol flags (pr_flags) */
#define PR_ATOMIC       0x0001      /* Exchange atomic messages */
#define PR_ADDR         0x0002      /* Addresses given with messages */
#define PR_CONNREQUIRED 0x0004      /* Connection required */
#define PR_WANTRCVD     0x0008      /* Want PRU_RCVD calls */
#define PR_RIGHTS       0x0010      /* Passes access rights */
#define PR_IMPLOPCL     0x0020      /* Implied open/close */
#define PR_LASTHDR      0x0040      /* Enforce LASTHDRflag for IPv6 */
#define PR_LISTEN       0x0080      /* Supports listen() */

/*
 * Simple mbuf structure (simplified from 4.4BSD)
 * For buffer management without full BSD mbuf complexity
 */
#define MLEN        256             /* Normal data length */
#define MHLEN       (MLEN - sizeof(struct m_hdr))  /* Data with header */
#define MINCLSIZE   (MHLEN + 1)     /* Min cluster size */
#define MCLBYTES    2048            /* Cluster size */

struct m_hdr {
    struct mbuf    *mh_next;        /* Next buffer in chain */
    struct mbuf    *mh_nextpkt;     /* Next packet in list */
    char           *mh_data;        /* Location of data */
    uint32_t        mh_len;         /* Amount of data in buffer */
    uint16_t        mh_type;        /* Type of data */
    uint16_t        mh_flags;       /* Flags */
};

struct mbuf {
    struct m_hdr    m_hdr;
    union {
        struct {
            struct socket  *mh_so;      /* Socket for recv */
            struct sockaddr *mh_daddr;  /* Dest addr */
        } m_pkthdr;
        char m_dat[MLEN];               /* Data storage */
    } m_dat;
};

/* mbuf access macros */
#define m_next      m_hdr.mh_next
#define m_nextpkt   m_hdr.mh_nextpkt
#define m_data      m_hdr.mh_data
#define m_len       m_hdr.mh_len
#define m_type      m_hdr.mh_type
#define m_flags     m_hdr.mh_flags

/* mbuf types */
#define MT_FREE     0               /* Should be on free list */
#define MT_DATA     1               /* Dynamic data */
#define MT_HEADER   2               /* Packet header */
#define MT_SONAME   8               /* Socket name */
#define MT_CONTROL  14              /* Extra-data protocol message */
#define MT_OOBDATA  15              /* Expedited data */

/* mbuf flags */
#define M_EXT       0x0001          /* Has external storage */
#define M_PKTHDR    0x0002          /* Has packet header */
#define M_EOR       0x0004          /* End of record */
#define M_BCAST     0x0100          /* Broadcast packet */
#define M_MCAST     0x0200          /* Multicast packet */

/*
 * Socket creation and management functions
 */

/* Socket lifecycle */
int     socreate(int domain, struct socket **so, int type, int protocol);
int     sobind(struct socket *so, struct sockaddr *nam, size_t namlen);
int     solisten(struct socket *so, int backlog);
int     soconnect(struct socket *so, struct sockaddr *nam, size_t namlen);
int     soaccept(struct socket *so, struct sockaddr *nam);
int     sodisconnect(struct socket *so);
int     soclose(struct socket *so);
int     soabort(struct socket *so);

/* Data transfer (4.4BSD style) */
int     sosend(struct socket *so, struct sockaddr *addr,
               uio_t *uio, struct mbuf *top,
               struct mbuf *control, int flags);
int     soreceive(struct socket *so, struct sockaddr **paddr,
                  uio_t *uio, struct mbuf **mp0,
                  struct mbuf **controlp, int *flagsp);

/* Socket buffer operations */
void    sbinit(struct sockbuf *sb, uint32_t hiwat);
void    sbrelease(struct sockbuf *sb);
int     sbappend(struct sockbuf *sb, struct mbuf *m);
int     sbappendaddr(struct sockbuf *sb, struct sockaddr *asa,
                     struct mbuf *m0, struct mbuf *control);
void    sbflush(struct sockbuf *sb);
void    sbdrop(struct sockbuf *sb, int len);

/* Socket option handling */
int     sosetopt(struct socket *so, int level, int optname,
                 const void *optval, socklen_t optlen);
int     sogetopt(struct socket *so, int level, int optname,
                 void *optval, socklen_t *optlen);

/* Wakeup and notification */
void    sowakeup(struct socket *so, struct sockbuf *sb);
void    sorwakeup(struct socket *so);
void    sowwakeup(struct socket *so);

/* Exokernel capability integration */
int     sopledge(struct socket *so, uint32_t promises);
int     socheck_promise(struct socket *so, uint32_t promise);
int     socap_attach(struct socket *so, void *cap);

/* mbuf operations */
struct mbuf *m_get(int how, int type);
struct mbuf *m_gethdr(int how, int type);
void    m_free(struct mbuf *m);
void    m_freem(struct mbuf *m);
struct mbuf *m_copym(struct mbuf *m, int off, int len, int how);
struct mbuf *m_pullup(struct mbuf *m, int len);
void    m_adj(struct mbuf *m, int len);

/* Allocation hints for m_get */
#define M_DONTWAIT  1               /* Don't wait for memory */
#define M_WAIT      0               /* Ok to wait for memory */
#define M_NOWAIT    M_DONTWAIT      /* Alias */

/* mbuf data access macro */
#define mtod(m, t)  ((t)((m)->m_data))

/* Socket state transitions */
void    soisconnected(struct socket *so);
void    soisconnecting(struct socket *so);
void    soisdisconnected(struct socket *so);
void    soisdisconnecting(struct socket *so);
void    socantsendmore(struct socket *so);
void    socantrcvmore(struct socket *so);

/* Additional socket buffer operations */
int     sbappendcontrol(struct sockbuf *sb, struct mbuf *m0, struct mbuf *control);
int     sbreserve(struct sockbuf *sb, uint32_t cc);
void    sbwait(struct sockbuf *sb);
void    sbwakeup(struct sockbuf *sb);

/* Unix domain socket internalization/externalization */
int     unp_internalize(struct mbuf *control);
int     unp_externalize(struct mbuf *control);

/* Control message macros (for SCM_RIGHTS, SCM_CREDS) */
#ifndef CMSG_ALIGN
#define CMSG_ALIGN(len)     (((len) + sizeof(long) - 1) & ~(sizeof(long) - 1))
#endif
#ifndef CMSG_DATA
#define CMSG_DATA(cmsg)     ((unsigned char *)((cmsg) + 1))
#endif

/* Control message types (guard to avoid system header conflicts) */
#ifndef SCM_RIGHTS
#define SCM_RIGHTS      0x01        /* File descriptor passing */
#endif
#ifndef SCM_CREDS
#define SCM_CREDS       0x02        /* Credential passing */
#endif
#ifndef SCM_TIMESTAMP_BSD
#define SCM_TIMESTAMP_BSD   0x04    /* Timestamp (BSD socket layer) */
#endif

/* Domain family aliases */
#ifndef AF_LOCAL
#define AF_LOCAL    AF_UNIX
#endif

#endif /* _LIBOS_SOCKETVAR_H_ */
