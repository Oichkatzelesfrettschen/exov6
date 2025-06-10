#pragma once
#include <stdint.h>

/* Minimal 9P client helpers. */

/* Connect to a 9P server and perform a version handshake. */
int p9_connect(const char *addr, uint16_t port, uint32_t msize);

/* Close the 9P connection. */
int p9_disconnect(int fd);

