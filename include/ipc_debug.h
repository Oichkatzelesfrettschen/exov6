#pragma once

#ifdef IPC_DEBUG
#ifdef EXO_KERNEL
#include "defs.h"
#define IPC_LOG(fmt, ...) cprintf("IPC: " fmt "\n", ##__VA_ARGS__)
#else
extern int printf(int fd, const char *fmt, ...);
#define IPC_LOG(fmt, ...) printf(1, "IPC: " fmt "\n", ##__VA_ARGS__)
#endif
#else
#define IPC_LOG(fmt, ...) ((void)0)
#endif

