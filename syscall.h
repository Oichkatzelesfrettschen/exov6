#pragma once

// System call numbers
#define SYS_fork    1
#define SYS_exit    2
#define SYS_wait    3
#define SYS_pipe    4
#define SYS_read    5
#define SYS_kill    6
#define SYS_exec    7
#define SYS_fstat   8
#define SYS_chdir   9
#define SYS_dup    10
#define SYS_getpid 11
#define SYS_sbrk   12
#define SYS_sleep  13
#define SYS_uptime 14
#define SYS_open   15
#define SYS_write  16
#define SYS_mknod  17
#define SYS_unlink 18
#define SYS_link   19
#define SYS_mkdir  20
#define SYS_close  21
#define SYS_mappte 22
#define SYS_set_timer_upcall 23
#define SYS_exo_alloc_page 24
#define SYS_exo_unbind_page 25
#define SYS_exo_alloc_block 26
#define SYS_exo_bind_block 27
#define SYS_exo_flush_block 28
#define SYS_exo_yield_to 29
#define SYS_exo_read_disk 30
#define SYS_exo_write_disk 31
#define SYS_exo_send 32
#define SYS_exo_recv 33
#define SYS_endpoint_send 34
#define SYS_endpoint_recv 35
#define SYS_proc_alloc 36
#define SYS_set_gas 37
#define SYS_get_gas 38
#define SYS_set_numa_node 39
#define SYS_ipc_fast 0x30
#define SYS_fcntl 0x31
#define SYS_sigsend 0x32
#define SYS_sigcheck 0x33

