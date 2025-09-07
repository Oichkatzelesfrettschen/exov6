#pragma once

/**
 * @file sys/time.h
 * @brief POSIX time interface for exokernel
 */

#include <stddef.h>
#include <stdint.h>
#include <sys/types.h>

/* struct timeval is already defined in sys/types.h */

struct timezone {
    int tz_minuteswest;  /* minutes west of Greenwich */
    int tz_dsttime;      /* type of DST correction */
};

/* Function declarations */
int gettimeofday(struct timeval *tv, struct timezone *tz);
int settimeofday(const struct timeval *tv, const struct timezone *tz);

/* Obsolete - use select() instead */
int select(int nfds, fd_set *readfds, fd_set *writefds, fd_set *exceptfds, struct timeval *timeout);