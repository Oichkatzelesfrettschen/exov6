#pragma once

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
