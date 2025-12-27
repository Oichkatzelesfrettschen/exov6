/**
 * @file lib9p.c
 * @brief Host-backed 9P protocol stubs for user-space demos
 *
 * This file provides host implementation of the 9P protocol client.
 * It's completely standalone and doesn't depend on any kernel code.
 */

/* Include system headers FIRST to avoid conflicts with project headers */
#define _GNU_SOURCE
#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

/* Basic structures for the version handshake */
struct p9_hdr {
    uint32_t size;
    uint8_t type;
    uint16_t tag;
};

struct p9_version {
    struct p9_hdr hdr;
    uint32_t msize;
    char version[6];
};

/**
 * Establish a TCP connection and negotiate 9P version.
 */
int p9_connect(const char *addr, uint16_t port, uint32_t msize) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0)
        return -1;

    struct sockaddr_in sin;
    memset(&sin, 0, sizeof(sin));
    sin.sin_family = AF_INET;
    sin.sin_port = htons(port);
    if (inet_aton(addr, &sin.sin_addr) == 0) {
        close(fd);
        return -1;
    }

    if (connect(fd, (struct sockaddr *)&sin, sizeof(sin)) < 0) {
        close(fd);
        return -1;
    }

    /* Send Tversion */
    struct p9_version tv;
    memset(&tv, 0, sizeof(tv));
    tv.hdr.size = sizeof(tv);
    tv.hdr.type = 100;  /* Tversion */
    tv.hdr.tag = 0xffff;
    tv.msize = msize;
    memcpy(tv.version, "9P2000", 6);

    if (write(fd, &tv, sizeof(tv)) != (ssize_t)sizeof(tv)) {
        close(fd);
        return -1;
    }

    /* Receive Rversion */
    struct p9_version rv;
    if (read(fd, &rv, sizeof(rv)) != (ssize_t)sizeof(rv)) {
        close(fd);
        return -1;
    }

    if (rv.hdr.type != 101) {  /* Rversion */
        close(fd);
        return -1;
    }

    return fd;
}

/**
 * Close the socket connection.
 */
int p9_disconnect(int fd) {
    if (fd >= 0)
        close(fd);
    return 0;
}
