#pragma once

/**
 * @file sys/resource.h
 * @brief POSIX resource limits - minimal implementation for exokernel
 */

#include <stddef.h>

typedef unsigned long rlim_t;

struct rlimit {
    rlim_t rlim_cur;  /* Current (soft) limit */
    rlim_t rlim_max;  /* Maximum value for rlim_cur */
};

/* Resource types */
#define RLIMIT_CPU      0   /* CPU time in seconds */
#define RLIMIT_FSIZE    1   /* Maximum file size */
#define RLIMIT_DATA     2   /* Data segment size */
#define RLIMIT_STACK    3   /* Stack size */
#define RLIMIT_CORE     4   /* Core file size */
#define RLIMIT_RSS      5   /* Resident set size */
#define RLIMIT_NPROC    6   /* Number of processes */
#define RLIMIT_NOFILE   7   /* Number of open files */
#define RLIMIT_MEMLOCK  8   /* Locked-in-memory address space */
#define RLIMIT_AS       9   /* Address space limit */

#define RLIM_NLIMITS    10

/* Special values for limits */
#define RLIM_INFINITY   (~(rlim_t)0)
#define RLIM_SAVED_MAX  RLIM_INFINITY
#define RLIM_SAVED_CUR  RLIM_INFINITY

/* Function declarations */
int getrlimit(int resource, struct rlimit *rlp);
int setrlimit(int resource, const struct rlimit *rlp);