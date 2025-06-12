#include "libos/lib9p.h"
#include <arpa/inet.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <stdlib.h>

/* Basic structures for the version handshake. */
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

/* Establish a TCP connection and negotiate 9P version. */
int p9_connect(const char *addr, uint16_t port, uint32_t msize) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0)
    return -1;
  struct sockaddr_in sin = {0};
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
  struct p9_version tv = {0};
  tv.hdr.size = sizeof(tv);
  tv.hdr.type = 100; /* Tversion */
  tv.hdr.tag = 0xffff;
  tv.msize = msize;
  memcpy(tv.version, "9P2000", 6);
  if (write(fd, &tv, sizeof(tv)) != (ssize_t)sizeof(tv)) {
    close(fd);
    return -1;
  }
  struct p9_version rv;
  if (read(fd, &rv, sizeof(rv)) != (ssize_t)sizeof(rv)) {
    close(fd);
    return -1;
  }
  if (rv.hdr.type != 101) { /* Rversion */
    close(fd);
    return -1;
  }
  return fd;
}

/* Close the socket connection. */
int p9_disconnect(int fd) {
  if (fd >= 0)
    close(fd);
  return 0;
}

