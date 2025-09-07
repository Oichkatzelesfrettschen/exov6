#pragma once

#ifdef __ASSEMBLER__
// Assembly-friendly definitions
#define SYS_fork                1
#define SYS_exit                2
#define SYS_wait                3
#define SYS_pipe                4
#define SYS_kill                5
#define SYS_exec                6
#define SYS_getpid              7
#define SYS_sbrk                8
#define SYS_sleep               9
#define SYS_uptime              10
#define SYS_mappte              11
#define SYS_set_timer_upcall    12
#define SYS_exo_alloc_page      13
#define SYS_exo_unbind_page     14
#define SYS_exo_alloc_block     15
#define SYS_exo_bind_block      16
#define SYS_exo_flush_block     17
#define SYS_exo_yield_to        18
#define SYS_exo_read_disk       19
#define SYS_exo_write_disk      20
#define SYS_exo_send            21
#define SYS_exo_recv            22
#define SYS_exo_recv_timed      23
#define SYS_endpoint_send       24
#define SYS_endpoint_recv       25
#define SYS_proc_alloc          26
#define SYS_set_gas             27
#define SYS_get_gas             28
#define SYS_set_numa_node       29
#define SYS_fcntl               30
#define SYS_sigsend             31
#define SYS_sigcheck            32
#define SYS_cap_inc             33
#define SYS_cap_dec             34
#define SYS_ipc                 35
#define SYS_exo_irq_alloc       36
#define SYS_exo_irq_wait        37
#define SYS_exo_irq_ack         38
#define SYS_exo_alloc_ioport    39
#define SYS_exo_bind_irq        40
#define SYS_exo_alloc_dma       41
#define SYS_exo_alloc_hypervisor 42
#define SYS_hv_launch           43
#define SYS_service_register    44
#define SYS_service_add_dependency 45
#else
// C enum for kernel code
enum {
  SYS_fork = 1,
  SYS_exit,
  SYS_wait,
  SYS_pipe,
  SYS_kill,
  SYS_exec,
  SYS_getpid,
  SYS_sbrk,
  SYS_sleep,
  SYS_uptime,
  SYS_mappte,
  SYS_set_timer_upcall,
  SYS_exo_alloc_page,
  SYS_exo_unbind_page,
  SYS_exo_alloc_block,
  SYS_exo_bind_block,
  SYS_exo_flush_block,
  SYS_exo_yield_to,
  SYS_exo_read_disk,
  SYS_exo_write_disk,
  SYS_exo_send,
  SYS_exo_recv,
  SYS_exo_recv_timed,
  SYS_endpoint_send,
  SYS_endpoint_recv,
  SYS_proc_alloc,
  SYS_set_gas,
  SYS_get_gas,
  SYS_set_numa_node,
  SYS_fcntl,
  SYS_sigsend,
  SYS_sigcheck,
  SYS_cap_inc,
  SYS_cap_dec,
  SYS_ipc,
  SYS_exo_irq_alloc,
  SYS_exo_irq_wait,
  SYS_exo_irq_ack,
  SYS_exo_alloc_ioport,
  SYS_exo_bind_irq,
  SYS_exo_alloc_dma,
  SYS_exo_alloc_hypervisor,
  SYS_hv_launch,
  SYS_service_register,
  SYS_service_add_dependency,
};
#endif
