// kernel/sys/sysfile.c
// The Great Purge: High-level filesystem syscalls are removed in Exokernel mode.

#include <types.h>
#include "defs.h"
#include "param.h"
#include "mmu.h"
#include "proc.h"

/*
 * Legacy UNIX syscalls removed:
 * sys_open, sys_read, sys_write, sys_close, sys_dup, sys_link, sys_unlink,
 * sys_mkdir, sys_chdir, sys_fstat, sys_pipe, sys_mknod
 */
