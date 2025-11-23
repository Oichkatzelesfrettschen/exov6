/**
 * @file inet_domain.c
 * @brief Internet Protocol Domain (AF_INET)
 *
 * Implements the TCP and UDP protocol handlers.
 * Synthesized from BSD network stacks with exokernel integration.
 */

#include "socketvar.h"
#include "protosw.h"
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <netinet/in.h>

/* Protocol control block hash tables */
#define INPCB_HASH_SIZE     256
static struct inpcb *inpcb_hash[INPCB_HASH_SIZE];
static struct inpcb *inpcb_bind_hash[INPCB_HASH_SIZE];

/* Port allocation */
static uint16_t next_ephemeral_port = 49152;
#define EPHEMERAL_PORT_MIN  49152
#define EPHEMERAL_PORT_MAX  65535

/* Hash function for port lookup */
static inline unsigned int
inpcb_hash_port(uint16_t port)
{
    return port % INPCB_HASH_SIZE;
}

/* Allocate an internet PCB */
static struct inpcb *
inpcb_alloc(struct socket *so)
{
    struct inpcb *inp = malloc(sizeof(struct inpcb));
    if (inp == NULL)
        return NULL;

    memset(inp, 0, sizeof(*inp));
    inp->inp_socket = so;
    so->so_pcb = inp;

    inp->inp_ip_ttl = 64;       /* Default TTL */
    inp->inp_ip_tos = 0;

    return inp;
}

/* Free an internet PCB */
static void
inpcb_free(struct inpcb *inp)
{
    if (inp == NULL)
        return;

    /* Remove from hash tables */
    if (inp->inp_hash_prev) {
        *inp->inp_hash_prev = inp->inp_hash_next;
        if (inp->inp_hash_next)
            inp->inp_hash_next->inp_hash_prev = inp->inp_hash_prev;
    }

    /* Free protocol-specific PCB */
    if (inp->inp_ppcb)
        free(inp->inp_ppcb);

    free(inp);
}

/* Allocate an ephemeral port */
static uint16_t
inpcb_alloc_port(void)
{
    uint16_t port = next_ephemeral_port++;
    if (next_ephemeral_port > EPHEMERAL_PORT_MAX)
        next_ephemeral_port = EPHEMERAL_PORT_MIN;
    return htons(port);
}

/* Bind an internet PCB to an address */
static int
inpcb_bind(struct inpcb *inp, struct sockaddr_in *sin)
{
    if (sin == NULL) {
        /* Bind to any address, ephemeral port */
        inp->inp_laddr.sin_addr.s_addr = INADDR_ANY;
        inp->inp_lport = inpcb_alloc_port();
    } else {
        inp->inp_laddr = *sin;
        if (sin->sin_port == 0)
            inp->inp_lport = inpcb_alloc_port();
        else
            inp->inp_lport = sin->sin_port;
    }

    /* Add to bind hash */
    unsigned int hash = inpcb_hash_port(ntohs(inp->inp_lport));
    inp->inp_hash_next = inpcb_bind_hash[hash];
    if (inpcb_bind_hash[hash])
        inpcb_bind_hash[hash]->inp_hash_prev = &inp->inp_hash_next;
    inp->inp_hash_prev = &inpcb_bind_hash[hash];
    inpcb_bind_hash[hash] = inp;

    return 0;
}

/* Connect an internet PCB to a remote address */
static int
inpcb_connect(struct inpcb *inp, struct sockaddr_in *sin)
{
    if (sin == NULL)
        return EINVAL;

    /* Bind to ephemeral port if not bound */
    if (inp->inp_lport == 0)
        inpcb_bind(inp, NULL);

    inp->inp_faddr = *sin;
    inp->inp_fport = sin->sin_port;

    return 0;
}

/*
 * TCP Protocol Implementation
 */

static struct tcpcb *
tcp_newtcpcb(struct inpcb *inp)
{
    struct tcpcb *tp = malloc(sizeof(struct tcpcb));
    if (tp == NULL)
        return NULL;

    memset(tp, 0, sizeof(*tp));
    tp->t_socket = inp->inp_socket;
    tp->t_state = TCPS_CLOSED;
    tp->t_maxseg = 1460;        /* Default MSS */
    tp->snd_cwnd = 2 * tp->t_maxseg;
    tp->snd_ssthresh = 65535;

    inp->inp_ppcb = tp;
    return tp;
}

int
tcp_attach(struct socket *so, int proto)
{
    struct inpcb *inp;
    struct tcpcb *tp;

    inp = inpcb_alloc(so);
    if (inp == NULL)
        return ENOBUFS;

    tp = tcp_newtcpcb(inp);
    if (tp == NULL) {
        inpcb_free(inp);
        return ENOBUFS;
    }

    return 0;
}

int
tcp_detach(struct socket *so)
{
    struct inpcb *inp = so->so_pcb;
    if (inp == NULL)
        return 0;

    so->so_pcb = NULL;
    inpcb_free(inp);
    return 0;
}

int
tcp_bind(struct socket *so, struct sockaddr *nam, size_t namlen)
{
    struct inpcb *inp = so->so_pcb;
    if (inp == NULL)
        return EINVAL;

    if (namlen < sizeof(struct sockaddr_in))
        return EINVAL;

    return inpcb_bind(inp, (struct sockaddr_in *)nam);
}

int
tcp_listen(struct socket *so, int backlog)
{
    struct inpcb *inp = so->so_pcb;
    struct tcpcb *tp;

    if (inp == NULL)
        return EINVAL;

    tp = inp->inp_ppcb;
    if (tp == NULL)
        return EINVAL;

    /* Auto-bind if not bound */
    if (inp->inp_lport == 0)
        inpcb_bind(inp, NULL);

    tp->t_state = TCPS_LISTEN;
    so->so_options |= SO_ACCEPTCONN;

    return 0;
}

int
tcp_connect(struct socket *so, struct sockaddr *nam, size_t namlen)
{
    struct inpcb *inp = so->so_pcb;
    struct tcpcb *tp;
    int error;

    if (inp == NULL)
        return EINVAL;

    tp = inp->inp_ppcb;
    if (tp == NULL)
        return EINVAL;

    if (namlen < sizeof(struct sockaddr_in))
        return EINVAL;

    error = inpcb_connect(inp, (struct sockaddr_in *)nam);
    if (error)
        return error;

    /* Start TCP handshake */
    tp->t_state = TCPS_SYN_SENT;
    atomic_fetch_or(&so->so_state, SS_ISCONNECTING);

    /* Generate ISS */
    tp->iss = (uint32_t)rand();
    tp->snd_una = tp->iss;
    tp->snd_nxt = tp->iss + 1;

    /* In real implementation, would send SYN here */
    /* For now, simulate immediate connection */
    tp->t_state = TCPS_ESTABLISHED;
    atomic_fetch_and(&so->so_state, ~SS_ISCONNECTING);
    atomic_fetch_or(&so->so_state, SS_ISCONNECTED);

    return 0;
}

int
tcp_accept(struct socket *so, struct sockaddr *nam)
{
    struct inpcb *inp = so->so_pcb;
    if (inp == NULL)
        return EINVAL;

    if (nam) {
        memcpy(nam, &inp->inp_faddr, sizeof(struct sockaddr_in));
    }

    return 0;
}

int
tcp_send(struct socket *so, struct mbuf *m, struct sockaddr *addr,
         struct mbuf *control)
{
    /* Append to send buffer */
    int error = sbappend(&so->so_snd, m);
    if (error)
        return error;

    /* In real implementation, would trigger TCP output */
    /* For now, just acknowledge the data */
    sowwakeup(so);

    return 0;
}

int
tcp_shutdown(struct socket *so)
{
    struct inpcb *inp = so->so_pcb;
    struct tcpcb *tp;

    if (inp == NULL)
        return EINVAL;

    tp = inp->inp_ppcb;
    if (tp == NULL)
        return EINVAL;

    /* Transition to closing state */
    switch (tp->t_state) {
    case TCPS_ESTABLISHED:
        tp->t_state = TCPS_FIN_WAIT_1;
        break;
    case TCPS_CLOSE_WAIT:
        tp->t_state = TCPS_LAST_ACK;
        break;
    }

    return 0;
}

int
tcp_sockaddr(struct socket *so, struct sockaddr *nam)
{
    struct inpcb *inp = so->so_pcb;
    if (inp == NULL)
        return EINVAL;

    memcpy(nam, &inp->inp_laddr, sizeof(struct sockaddr_in));
    ((struct sockaddr_in *)nam)->sin_port = inp->inp_lport;
    return 0;
}

int
tcp_peeraddr(struct socket *so, struct sockaddr *nam)
{
    struct inpcb *inp = so->so_pcb;
    if (inp == NULL)
        return EINVAL;

    memcpy(nam, &inp->inp_faddr, sizeof(struct sockaddr_in));
    ((struct sockaddr_in *)nam)->sin_port = inp->inp_fport;
    return 0;
}

/*
 * UDP Protocol Implementation
 */

int
udp_attach(struct socket *so, int proto)
{
    struct inpcb *inp = inpcb_alloc(so);
    if (inp == NULL)
        return ENOBUFS;

    struct udpcb *up = malloc(sizeof(struct udpcb));
    if (up == NULL) {
        inpcb_free(inp);
        return ENOBUFS;
    }

    memset(up, 0, sizeof(*up));
    up->u_socket = so;
    inp->inp_ppcb = up;

    return 0;
}

int
udp_detach(struct socket *so)
{
    struct inpcb *inp = so->so_pcb;
    if (inp == NULL)
        return 0;

    so->so_pcb = NULL;
    inpcb_free(inp);
    return 0;
}

int
udp_bind(struct socket *so, struct sockaddr *nam, size_t namlen)
{
    struct inpcb *inp = so->so_pcb;
    if (inp == NULL)
        return EINVAL;

    if (namlen < sizeof(struct sockaddr_in))
        return EINVAL;

    return inpcb_bind(inp, (struct sockaddr_in *)nam);
}

int
udp_connect(struct socket *so, struct sockaddr *nam, size_t namlen)
{
    struct inpcb *inp = so->so_pcb;
    if (inp == NULL)
        return EINVAL;

    if (namlen < sizeof(struct sockaddr_in))
        return EINVAL;

    int error = inpcb_connect(inp, (struct sockaddr_in *)nam);
    if (error)
        return error;

    atomic_fetch_or(&so->so_state, SS_ISCONNECTED);
    return 0;
}

int
udp_send(struct socket *so, struct mbuf *m, struct sockaddr *addr,
         struct mbuf *control)
{
    struct inpcb *inp = so->so_pcb;
    if (inp == NULL) {
        m_freem(m);
        return EINVAL;
    }

    /* For unconnected sockets, require destination */
    if (addr == NULL && inp->inp_fport == 0) {
        m_freem(m);
        return EDESTADDRREQ;
    }

    /* In real implementation, would build UDP header and send */
    /* For now, just acknowledge */
    m_freem(m);
    return 0;
}

/*
 * Protocol switch entries
 */

static struct protosw tcp_protosw = {
    .pr_type = SOCK_STREAM,
    .pr_protocol = IPPROTO_TCP,
    .pr_flags = PR_CONNREQUIRED | PR_WANTRCVD | PR_LISTEN,
    .pr_domain = AF_INET,
    .pr_attach = tcp_attach,
    .pr_detach = tcp_detach,
    .pr_bind = tcp_bind,
    .pr_listen = tcp_listen,
    .pr_connect = tcp_connect,
    .pr_accept = tcp_accept,
    .pr_send = tcp_send,
    .pr_shutdown = tcp_shutdown,
    .pr_sockaddr = tcp_sockaddr,
    .pr_peeraddr = tcp_peeraddr,
};

static struct protosw udp_protosw = {
    .pr_type = SOCK_DGRAM,
    .pr_protocol = IPPROTO_UDP,
    .pr_flags = PR_ATOMIC | PR_ADDR,
    .pr_domain = AF_INET,
    .pr_attach = udp_attach,
    .pr_detach = udp_detach,
    .pr_bind = udp_bind,
    .pr_connect = udp_connect,
    .pr_send = udp_send,
};

static struct protosw inet_protosw[] = {
    /* TCP */
    {
        .pr_type = SOCK_STREAM,
        .pr_protocol = IPPROTO_TCP,
        .pr_flags = PR_CONNREQUIRED | PR_WANTRCVD | PR_LISTEN,
        .pr_domain = AF_INET,
        .pr_attach = tcp_attach,
        .pr_detach = tcp_detach,
        .pr_bind = tcp_bind,
        .pr_listen = tcp_listen,
        .pr_connect = tcp_connect,
        .pr_accept = tcp_accept,
        .pr_send = tcp_send,
        .pr_shutdown = tcp_shutdown,
        .pr_sockaddr = tcp_sockaddr,
        .pr_peeraddr = tcp_peeraddr,
    },
    /* UDP */
    {
        .pr_type = SOCK_DGRAM,
        .pr_protocol = IPPROTO_UDP,
        .pr_flags = PR_ATOMIC | PR_ADDR,
        .pr_domain = AF_INET,
        .pr_attach = udp_attach,
        .pr_detach = udp_detach,
        .pr_bind = udp_bind,
        .pr_connect = udp_connect,
        .pr_send = udp_send,
    },
};

/*
 * Internet domain
 */

static void
inet_init(void)
{
    tcp_init();
    udp_init();
}

struct domain inetdomain = {
    .dom_family = AF_INET,
    .dom_name = "internet",
    .dom_init = inet_init,
    .dom_protosw = inet_protosw,
    .dom_protoswend = &inet_protosw[sizeof(inet_protosw)/sizeof(inet_protosw[0])],
};

void
tcp_init(void)
{
    /* Initialize TCP timers, etc. */
}

void
udp_init(void)
{
    /* Initialize UDP state */
}

/*
 * Register the internet domain
 */
__attribute__((constructor))
static void
inet_domain_register(void)
{
    domain_add(&inetdomain);
}
