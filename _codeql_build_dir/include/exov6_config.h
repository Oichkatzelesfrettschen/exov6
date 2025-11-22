#ifndef EXOV6_CONFIG_H
#define EXOV6_CONFIG_H

/* Project Information */
#define EXOV6_PROJECT_NAME "PhoenixExokernel"
#define EXOV6_VERSION_MAJOR 1
#define EXOV6_VERSION_MINOR 0
#define EXOV6_VERSION_PATCH 0
#define EXOV6_VERSION "1.0.0"

/* Legacy Phoenix compatibility */
#define PHOENIX_CONFIG_H
#define PHOENIX_VERSION "1.0.0"

/* System capabilities */
#define HAVE_STDATOMIC_H 1
#define HAVE_STDNORETURN_H 1
#define HAVE_THREADS_H 1
#define HAVE_STDALIGN_H 1
#define HAVE_SYS_MMAN_H 1
#define HAVE_SYS_PRCTL_H 1
#define HAVE_LINUX_SECCOMP_H 1

/* C23 features */
/* #undef HAVE_STATIC_ASSERT */
/* #undef HAVE_GENERIC */

/* System functions */
#define HAVE_MMAP 1
#define HAVE_MPROTECT 1
#define HAVE_PRCTL 1
/* #undef HAVE_SECCOMP */
#define HAVE_CLONE 1
#define HAVE_EPOLL 1
#define HAVE_EVENTFD 1
#define HAVE_SIGNALFD 1
#define HAVE_TIMERFD 1

/* Libraries */
#define HAVE_LIBRT 1
#define HAVE_LIBPTHREAD 1
/* #undef HAVE_LIBNUMA */

/* Type sizes */
#define SIZEOF_VOID_P 8
#define SIZEOF_LONG 8
#define SIZEOF_SIZE_T 8

/* SIMD capabilities */
#define HAVE_SSE2 1
/* #undef HAVE_AVX2 */
/* #undef HAVE_AVX512F */
/* #undef HAVE_NEON */
/* #undef HAVE_ALTIVEC */

/* Hardware features */
/* #undef HAVE_KVM */
/* #undef HAVE_HYPERVISOR */
/* #undef IN_CONTAINER */

/* System parameters */
#define CPU_COUNT 4
#define PAGE_SIZE 4096
#define MEMORY_SIZE_MB 15994

/* Phoenix Exokernel version */
#define PHOENIX_VERSION_MAJOR 1
#define PHOENIX_VERSION_MINOR 0
#define PHOENIX_VERSION_PATCH 0
#define PHOENIX_VERSION "1.0.0"

/* Build configuration */
/* #undef USE_LTO */
/* #undef USE_LLD */
/* #undef USE_POLLY */
/* #undef USE_SIMD */
/* #undef USE_TICKET_LOCK */
/* #undef USE_CAPNP */
/* #undef IPC_DEBUG */
/* #undef MCU */

/* Sanitizers */
/* #undef ENABLE_ASAN */
/* #undef ENABLE_TSAN */
/* #undef ENABLE_UBSAN */
/* #undef ENABLE_MSAN */

#endif /* PHOENIX_CONFIG_H */
