#pragma once
// Assembly-compatible syscall constants
// Generated from syscall.h enum values

#define SYS_fork 1
#define SYS_exit 2
#define SYS_wait 3
#define SYS_pipe 4
#define SYS_kill 5
#define SYS_exec 6
#define SYS_getpid 7
#define SYS_sbrk 8
#define SYS_sleep 9
#define SYS_uptime 10
#define SYS_mappte 11
#define SYS_set_timer_upcall 12
#define SYS_exo_alloc_page 13
#define SYS_exo_unbind_page 14
#define SYS_exo_alloc_block 15
#define SYS_exo_bind_block 16
#define SYS_exo_flush_block 17
#define SYS_exo_yield_to 18
#define SYS_exo_read_disk 19
#define SYS_exo_write_disk 20
#define SYS_exo_send 21
#define SYS_exo_recv 22
#define SYS_exo_recv_timed 23
#define SYS_endpoint_send 24
#define SYS_endpoint_recv 25
#define SYS_proc_alloc 26
#define SYS_set_gas 27
#define SYS_get_gas 28
#define SYS_set_numa_node 29
#define SYS_fcntl 30
#define SYS_sigsend 31
#define SYS_sigcheck 32
#define SYS_cap_inc 33
#define SYS_cap_dec 34
#define SYS_ipc 35
#define SYS_exo_alloc_ioport 36
#define SYS_exo_bind_irq 37
#define SYS_exo_alloc_dma 38
#define SYS_exo_alloc_hypervisor 39
#define SYS_hv_launch 40
#define SYS_exo_irq_alloc 41
#define SYS_exo_irq_wait 42
#define SYS_exo_irq_ack 43
#define SYS_service_register 44
#define SYS_service_add_dependency 45

// Missing POSIX system calls
#define SYS_read 46
#define SYS_write 47
#define SYS_close 48
#define SYS_open 49
#define SYS_mknod 50
#define SYS_unlink 51
#define SYS_fstat 52
#define SYS_link 53
#define SYS_mkdir 54
#define SYS_chdir 55
#define SYS_dup 56