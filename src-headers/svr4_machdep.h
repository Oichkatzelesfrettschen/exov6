#pragma once

#ifdef __cplusplus
extern "C" {
#endif
/* Machine dependent definitions for SVR4 compatibility on x86 */

/*
 * The definitions below originate from NetBSD's svr4_machdep.h
 * (revision 1.16, 2008/04/28).  They are included here to aid the
 * planned SVR4 personality layer in libos.
 */

#include <compat/svr4/svr4_types.h>

/* General register indices */
#define SVR4_X86_GS 0
#define SVR4_X86_FS 1
#define SVR4_X86_ES 2
#define SVR4_X86_DS 3
#define SVR4_X86_EDI 4
#define SVR4_X86_ESI 5
#define SVR4_X86_EBP 6
#define SVR4_X86_ESP 7
#define SVR4_X86_EBX 8
#define SVR4_X86_EDX 9
#define SVR4_X86_ECX 10
#define SVR4_X86_EAX 11
#define SVR4_X86_TRAPNO 12
#define SVR4_X86_ERR 13
#define SVR4_X86_EIP 14
#define SVR4_X86_CS 15
#define SVR4_X86_EFL 16
#define SVR4_X86_UESP 17
#define SVR4_X86_SS 18
#define SVR4_X86_MAXREG 19

typedef int svr4_greg_t;
typedef svr4_greg_t svr4_gregset_t[SVR4_X86_MAXREG];

/* FPU state container */
typedef struct {
  int f_x87[62];     /* x87 registers */
  long f_weitek[33]; /* weitek */
} svr4_fregset_t;

typedef struct svr4_mcontext {
  svr4_gregset_t greg;
  svr4_fregset_t freg;
} svr4_mcontext_t;

#define SVR4_UC_MACHINE_PAD 5

/* sysarch numbers */
#define SVR4_SYSARCH_FPHW 40
#define SVR4_SYSARCH_DSCR 75

struct svr4_ssd {
  unsigned int selector;
  unsigned int base;
  unsigned int limit;
  unsigned int access1;
  unsigned int access2;
};

/* Processor traps */
#define SVR4_T_DIVIDE 0
#define SVR4_T_TRCTRAP 1
#define SVR4_T_NMI 2
#define SVR4_T_BPTFLT 3
#define SVR4_T_OFLOW 4
#define SVR4_T_BOUND 5
#define SVR4_T_PRIVINFLT 6
#define SVR4_T_DNA 7
#define SVR4_T_DOUBLEFLT 8
#define SVR4_T_FPOPFLT 9
#define SVR4_T_TSSFLT 10
#define SVR4_T_SEGNPFLT 11
#define SVR4_T_STKFLT 12
#define SVR4_T_PROTFLT 13
#define SVR4_T_PAGEFLT 14
#define SVR4_T_ALIGNFLT 17

/* Fast syscall gate traps */
#define SVR4_TRAP_FNULL 0       /* Null trap, for testing */
#define SVR4_TRAP_FGETFP 1      /* Get emulated FP context */
#define SVR4_TRAP_FSETFP 2      /* Set emulated FP context */
#define SVR4_TRAP_GETHRTIME 3   /* implements gethrtime(2) */
#define SVR4_TRAP_GETHRVTIME 4  /* implements gethrvtime(2) */
#define SVR4_TRAP_GETHRESTIME 5 /* clock_gettime(CLOCK_REALTIME, tp) */

struct proc;
void svr4_syscall_intern(struct proc *);

#ifdef __cplusplus
}
#endif
