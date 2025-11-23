/**
 * @file protosw.h
 * @brief Protocol Switch and Domain Definitions
 *
 * BSD-style protocol registration and domain management.
 * Synthesized from 4.4BSD, NetBSD, and FreeBSD.
 *
 * @see socketvar.h for socket structures
 */

#ifndef _LIBOS_PROTOSW_H_
#define _LIBOS_PROTOSW_H_

#include <stdint.h>
#include <netinet/in.h>
#include <sys/un.h>
#include "socketvar.h"

/*
 * Protocol domain structure (from 4.4BSD struct domain)
 * Groups related protocols (e.g., AF_INET contains TCP, UDP, ICMP)
 */
struct domain {
    int         dom_family;         /* AF_* value */
    const char *dom_name;           /* Domain name (e.g., "internet") */

    /* Domain operations */
    void        (*dom_init)(void);              /* Domain initialization */
    int         (*dom_externalize)(struct mbuf *);  /* Externalize rights */
    void        (*dom_dispose)(struct mbuf *);  /* Dispose of rights */

    /* Protocol list */
    struct protosw *dom_protosw;    /* First protocol */
    struct protosw *dom_protoswend; /* Past last protocol */

    /* Domain linkage */
    struct domain  *dom_next;       /* Next domain in list */

    /* Route operations (FreeBSD style) */
    int         (*dom_rtattach)(void **, int);  /* Routing attach */
    int         dom_rtoffset;                   /* Offset into socket */
    int         dom_maxrtkey;                   /* Max routing key size */
};

/*
 * Protocol registration and lookup
 */

/* Register a protocol domain */
void    domain_add(struct domain *dp);

/* Find a protocol by family, type, and protocol number */
struct protosw *pffindtype(int family, int type);
struct protosw *pffindproto(int family, int protocol, int type);

/* Protocol initialization */
void    protocols_init(void);

/*
 * Protocol-specific control block types
 * Each protocol defines its own PCB structure
 */

/* TCP control block (minimal) */
struct tcpcb {
    struct socket  *t_socket;       /* Back pointer to socket */
    uint16_t        t_state;        /* TCP state */
    uint16_t        t_flags;        /* TCP flags */

    /* Sequence numbers */
    uint32_t        snd_una;        /* Send unacknowledged */
    uint32_t        snd_nxt;        /* Send next */
    uint32_t        snd_wl1;        /* Window update seq */
    uint32_t        snd_wl2;        /* Window update ack */
    uint32_t        snd_wnd;        /* Send window */
    uint32_t        rcv_nxt;        /* Receive next */
    uint32_t        rcv_wnd;        /* Receive window */
    uint32_t        iss;            /* Initial send seq */
    uint32_t        irs;            /* Initial receive seq */

    /* Timers */
    int16_t         t_rtt;          /* RTT */
    int16_t         t_srtt;         /* Smoothed RTT */
    int16_t         t_rttvar;       /* RTT variance */
    int16_t         t_rxtcur;       /* Current retransmit timeout */
    int16_t         t_maxseg;       /* Max segment size */

    /* Congestion control */
    uint32_t        snd_cwnd;       /* Congestion window */
    uint32_t        snd_ssthresh;   /* Slow start threshold */
};

/* TCP states */
#define TCPS_CLOSED         0       /* Closed */
#define TCPS_LISTEN         1       /* Listening for connection */
#define TCPS_SYN_SENT       2       /* Active, sent SYN */
#define TCPS_SYN_RECEIVED   3       /* Received SYN */
#define TCPS_ESTABLISHED    4       /* Established */
#define TCPS_CLOSE_WAIT     5       /* Received FIN, wait for close */
#define TCPS_FIN_WAIT_1     6       /* Sent FIN */
#define TCPS_CLOSING        7       /* Both sides sent FIN */
#define TCPS_LAST_ACK       8       /* Received FIN, sent FIN */
#define TCPS_FIN_WAIT_2     9       /* FIN acked, waiting for FIN */
#define TCPS_TIME_WAIT      10      /* Waiting for all packets to die */

/* UDP control block (minimal) */
struct udpcb {
    struct socket  *u_socket;       /* Back pointer to socket */
    uint16_t        u_flags;        /* UDP flags */
};

/* Unix domain control block */
struct unpcb {
    struct socket  *unp_socket;     /* Back pointer to socket */
    struct sockaddr_un *unp_addr;   /* Bound address */
    struct unpcb   *unp_conn;       /* Connected peer */
    struct socket  *unp_refs;       /* Referencing sockets */
    struct socket  *unp_nextref;    /* Next reference */
    int             unp_rights;     /* File descriptor rights */
};

/*
 * Internet protocol control block
 * Common base for TCP and UDP
 */
struct inpcb {
    /* Local and foreign addresses */
    struct sockaddr_in inp_laddr;   /* Local address */
    struct sockaddr_in inp_faddr;   /* Foreign address */
    uint16_t        inp_lport;      /* Local port (network order) */
    uint16_t        inp_fport;      /* Foreign port (network order) */

    /* Socket back pointer */
    struct socket  *inp_socket;     /* Associated socket */

    /* Protocol-specific pointer */
    void           *inp_ppcb;       /* TCP/UDP control block */

    /* Options */
    uint8_t         inp_ip_ttl;     /* Time to live */
    uint8_t         inp_ip_tos;     /* Type of service */
    uint16_t        inp_flags;      /* Flags */

    /* PCB hash linkage (FreeBSD style) */
    struct inpcb   *inp_hash_next;
    struct inpcb  **inp_hash_prev;
};

/* inpcb flags */
#define INP_RECVOPTS    0x0001      /* Receive incoming IP options */
#define INP_RECVRETOPTS 0x0002      /* Receive IP options for reply */
#define INP_RECVDSTADDR 0x0004      /* Receive IP dst address */
#define INP_HDRINCL     0x0008      /* User supplies IP header */
#define INP_REUSEADDR   0x0010      /* Reuse local address */
#define INP_REUSEPORT   0x0020      /* Reuse local port */
#define INP_ANONPORT    0x0040      /* Allocated anonymous port */
#define INP_TIMEWAIT    0x0080      /* In TIME_WAIT state */

/*
 * Protocol registration macros
 */

/* Declare a protocol switch entry */
#define PROTOSW_ENTRY(dom, type, proto, flags, pr_usrreq) \
    { .pr_type = (type), .pr_protocol = (proto), \
      .pr_flags = (flags), .pr_domain = (dom), \
      .pr_usrreq = (pr_usrreq) }

/*
 * Standard protocol IDs
 */
#define IPPROTO_IP      0           /* Dummy for IP */
#define IPPROTO_ICMP    1           /* ICMP */
#define IPPROTO_TCP     6           /* TCP */
#define IPPROTO_UDP     17          /* UDP */
#define IPPROTO_RAW     255         /* Raw IP */

/*
 * Built-in protocol initializers
 */
void    tcp_init(void);
void    udp_init(void);
void    unix_init(void);
void    raw_init(void);

/* Protocol request handlers */
int     tcp_usrreq(struct socket *so, int req, struct mbuf *m,
                   struct mbuf *nam, struct mbuf *control);
int     udp_usrreq(struct socket *so, int req, struct mbuf *m,
                   struct mbuf *nam, struct mbuf *control);
int     unix_usrreq(struct socket *so, int req, struct mbuf *m,
                    struct mbuf *nam, struct mbuf *control);

/* New-style protocol handlers */
int     tcp_attach(struct socket *so, int proto);
int     tcp_detach(struct socket *so);
int     tcp_bind(struct socket *so, struct sockaddr *nam, size_t namlen);
int     tcp_listen(struct socket *so, int backlog);
int     tcp_connect(struct socket *so, struct sockaddr *nam, size_t namlen);
int     tcp_accept(struct socket *so, struct sockaddr *nam);
int     tcp_send(struct socket *so, struct mbuf *m, struct sockaddr *addr,
                 struct mbuf *control);
int     tcp_shutdown(struct socket *so);

int     udp_attach(struct socket *so, int proto);
int     udp_detach(struct socket *so);
int     udp_bind(struct socket *so, struct sockaddr *nam, size_t namlen);
int     udp_connect(struct socket *so, struct sockaddr *nam, size_t namlen);
int     udp_send(struct socket *so, struct mbuf *m, struct sockaddr *addr,
                 struct mbuf *control);

int     unix_attach(struct socket *so, int proto);
int     unix_detach(struct socket *so);
int     unix_bind(struct socket *so, struct sockaddr *nam, size_t namlen);
int     unix_listen(struct socket *so, int backlog);
int     unix_connect(struct socket *so, struct sockaddr *nam, size_t namlen);
int     unix_accept(struct socket *so, struct sockaddr *nam);
int     unix_send(struct socket *so, struct mbuf *m, struct sockaddr *addr,
                  struct mbuf *control);
int     unix_shutdown(struct socket *so);

#endif /* _LIBOS_PROTOSW_H_ */
