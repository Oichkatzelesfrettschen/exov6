/**
 * @file syscall.h
 * @brief Wrapper header for syscall definitions
 */
#pragma once

/* Include the main exov6 interface which has syscall numbers */
#include <exov6_interface.h>

/* Additional syscall definitions for exokernel primitives */
#ifndef SYS_exo_alloc_page
#define SYS_exo_alloc_page      20
#define SYS_exo_unbind_page     21
#define SYS_exo_alloc_block     22
#define SYS_exo_bind_block      23
#define SYS_exo_flush_block     24
#define SYS_exo_yield_to        25
#define SYS_exo_send            26
#define SYS_exo_recv            27
#define SYS_exo_recv_timed      28
#define SYS_exo_read_disk       29
#define SYS_exo_write_disk      30
#define SYS_exo_alloc_ioport    31
#define SYS_exo_bind_irq        32
#define SYS_exo_alloc_dma       33
#define SYS_exo_alloc_hypervisor 34
#define SYS_hv_launch           35
#define SYS_cap_inc             36
#define SYS_cap_dec             37
#define SYS_exo_irq_alloc       38
#define SYS_exo_irq_wait        39
#define SYS_exo_irq_ack         40
#define SYS_service_register    41
#define SYS_service_add_dependency 42
#endif
