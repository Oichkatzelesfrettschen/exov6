#ifndef LIBOS_SOCKET_INT_H
#define LIBOS_SOCKET_INT_H

#include <sys/socket.h>
#include <netinet/in.h>

enum sock_state {
    SS_UNCONNECTED,
    SS_CONNECTING,
    SS_CONNECTED,
    SS_DISCONNECTING,
    SS_LISTENING
};

struct libos_sock {
    int domain;
    int type;
    int protocol;
    enum sock_state state;
    int backlog;
    struct sockaddr_storage local_addr;
    struct sockaddr_storage remote_addr;

    /* Mock buffer for loopback */
    char *rx_buf;
    size_t rx_len;
    size_t rx_cap;
    char *tx_buf;
    size_t tx_len;
    size_t tx_cap;

    /* Connection tracking */
    struct libos_sock *peer;              /* Connected peer */
    struct libos_sock *accept_queue[8];   /* Backlog for listening sockets */
    int accept_head;
    int accept_tail;
};

#endif
