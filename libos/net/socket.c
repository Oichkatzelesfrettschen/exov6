#include <sys/socket.h>
#include <netinet/in.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include "file.h"
#include "socket_int.h"

extern int libos_install_file(struct file *f);
extern struct file *libos_get_file(int fd);

#define MAX_LISTENERS 32
static struct libos_sock *listeners[MAX_LISTENERS];
static int num_listeners = 0;

static void register_listener(struct libos_sock *s) {
    if (num_listeners < MAX_LISTENERS) {
        listeners[num_listeners++] = s;
    }
}

static struct libos_sock *find_listener(uint16_t port) {
    for (int i = 0; i < num_listeners; i++) {
        struct sockaddr_in *sin = (struct sockaddr_in *)&listeners[i]->local_addr;
        if (sin->sin_port == port) return listeners[i];
    }
    return NULL;
}

void libos_sock_close(void *sock) {
    struct libos_sock *s = (struct libos_sock *)sock;
    if (s) {
        if (s->rx_buf) free(s->rx_buf);
        if (s->tx_buf) free(s->tx_buf);
        // Remove from listeners if present (TODO: simplified, assume no remove for now)
        free(s);
    }
}

int libos_socket(int domain, int type, int protocol) {
    struct file *f = filealloc();
    if (!f) return -ENOMEM;

    struct libos_sock *s = malloc(sizeof(struct libos_sock));
    if (!s) {
        // fileclose not needed as f is fresh and ref=1 (or 0?).
        // filealloc returns ref=1.
        // Calling fileclose(f) here is safe if we didn't attach s yet.
        free(f);
        return -ENOMEM;
    }
    memset(s, 0, sizeof(*s));
    s->domain = domain;
    s->type = type;
    s->protocol = protocol;
    s->state = SS_UNCONNECTED;

    // Default buffer size
    s->rx_cap = 4096;
    s->rx_buf = malloc(s->rx_cap);
    s->tx_cap = 4096;
    s->tx_buf = malloc(s->tx_cap);

    if (!s->rx_buf || !s->tx_buf) {
        libos_sock_close(s);
        free(f);
        return -ENOMEM;
    }

    f->type = FD_SOCKET;
    f->socket = s;
    f->readable = 1;
    f->writable = 1;
    f->ref = 1;

    int fd = libos_install_file(f);
    if (fd < 0) {
        libos_sock_close(s);
        free(f);
        return -ENFILE; // or -1
    }
    return fd;
}

int libos_bind(int fd, const struct sockaddr *addr, socklen_t len) {
    struct file *f = libos_get_file(fd);
    if (!f || f->type != FD_SOCKET) return -ENOTSOCK;
    struct libos_sock *s = (struct libos_sock *)f->socket;

    if (len > sizeof(s->local_addr)) return -EINVAL;
    memcpy(&s->local_addr, addr, len);
    return 0;
}

int libos_listen(int fd, int backlog) {
    struct file *f = libos_get_file(fd);
    if (!f || f->type != FD_SOCKET) return -ENOTSOCK;
    struct libos_sock *s = (struct libos_sock *)f->socket;

    s->state = SS_LISTENING;
    s->backlog = backlog;
    register_listener(s);
    return 0;
}

int libos_accept(int fd, struct sockaddr *addr, socklen_t *len) {
    struct file *f = libos_get_file(fd);
    if (!f || f->type != FD_SOCKET) return -ENOTSOCK;
    struct libos_sock *s = (struct libos_sock *)f->socket;

    if (s->state != SS_LISTENING) return -EINVAL;

    // Wait for connection (Blocking stub: return -EAGAIN if empty)
    if (s->accept_head == s->accept_tail) {
        return -EAGAIN;
    }

    struct libos_sock *client_peer = s->accept_queue[s->accept_head];
    s->accept_head = (s->accept_head + 1) % 8;

    // Create a new socket for the server side of this connection
    struct file *newf = filealloc();
    if (!newf) return -ENOMEM; // Loss of connection

    struct libos_sock *news = malloc(sizeof(struct libos_sock));
    if (!news) { free(newf); return -ENOMEM; }
    memset(news, 0, sizeof(*news));

    news->state = SS_CONNECTED;
    news->rx_cap = 4096; news->rx_buf = malloc(news->rx_cap);
    news->tx_cap = 4096; news->tx_buf = malloc(news->tx_cap);

    if (!news->rx_buf || !news->tx_buf) {
        libos_sock_close(news);
        free(newf);
        return -ENOMEM;
    }

    // Link peers
    news->peer = client_peer;
    client_peer->peer = news;
    client_peer->state = SS_CONNECTED; // Update client state

    newf->type = FD_SOCKET;
    newf->socket = news;
    newf->readable = 1;
    newf->writable = 1;
    newf->ref = 1;

    if (addr && len && *len >= sizeof(struct sockaddr_in)) {
        struct sockaddr_in *sin = (struct sockaddr_in*)addr;
        memcpy(sin, &client_peer->local_addr, sizeof(struct sockaddr_in)); // Copy client's local addr
        *len = sizeof(struct sockaddr_in);
    }

    return libos_install_file(newf);
}

int libos_connect(int fd, const struct sockaddr *addr, socklen_t len) {
    struct file *f = libos_get_file(fd);
    if (!f || f->type != FD_SOCKET) return -ENOTSOCK;
    struct libos_sock *s = (struct libos_sock *)f->socket;

    if (addr->sa_family == AF_INET) {
        struct sockaddr_in *sin = (struct sockaddr_in*)addr;
        struct libos_sock *listener = find_listener(sin->sin_port);
        if (listener) {
             // Add to listener's queue
             int next = (listener->accept_tail + 1) % 8;
             if (next == listener->accept_head) return -ECONNREFUSED; // Full

             listener->accept_queue[listener->accept_tail] = s;
             listener->accept_tail = next;

             s->state = SS_CONNECTING; // Wait for accept
             // Block until accepted? For now return 0 and assume accept happens fast or async
             return 0;
        }
    }

    return -ECONNREFUSED;
}

long libos_send(int fd, const void *buf, size_t len, int flags) {
    struct file *f = libos_get_file(fd);
    if (!f || f->type != FD_SOCKET) return -ENOTSOCK;
    struct libos_sock *s = (struct libos_sock *)f->socket;

    if (s->state != SS_CONNECTED || !s->peer) return -ENOTCONN;

    // Copy to PEER's rx buffer
    // Simplified: overwrite peer's RX buffer (lossy if full)
    struct libos_sock *peer = s->peer;
    if (len > peer->rx_cap) len = peer->rx_cap;
    memcpy(peer->rx_buf, buf, len);
    peer->rx_len = len;

    return len;
}

long libos_recv(int fd, void *buf, size_t len, int flags) {
    struct file *f = libos_get_file(fd);
    if (!f || f->type != FD_SOCKET) return -ENOTSOCK;
    struct libos_sock *s = (struct libos_sock *)f->socket;

    if (s->state != SS_CONNECTED) return -ENOTCONN;

    if (s->rx_len > 0) {
        if (len > s->rx_len) len = s->rx_len;
        memcpy(buf, s->rx_buf, len);
        s->rx_len = 0; // Consumed
        return len;
    }
    return -EAGAIN; // Non-blocking default for mock
}

long libos_sendto(int fd, const void *buf, size_t len, int flags, const struct sockaddr *dest_addr, socklen_t addrlen) {
    (void)addrlen;
    // For SOCK_STREAM, dest_addr is ignored if connected
    return libos_send(fd, buf, len, flags);
}

long libos_recvfrom(int fd, void *buf, size_t len, int flags, struct sockaddr *src_addr, socklen_t *addrlen) {
    long ret = libos_recv(fd, buf, len, flags);
    if (ret >= 0 && src_addr && addrlen) {
        struct file *f = libos_get_file(fd);
        if (f && f->type == FD_SOCKET) {
             struct libos_sock *s = (struct libos_sock *)f->socket;
             if (s->peer && *addrlen >= sizeof(struct sockaddr_in)) {
                 memcpy(src_addr, &s->peer->local_addr, sizeof(struct sockaddr_in));
                 *addrlen = sizeof(struct sockaddr_in);
             }
        }
    }
    return ret;
}
