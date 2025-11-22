/* signal.h - POSIX-2024 Signal Handling */
#ifndef _SIGNAL_H
#define _SIGNAL_H

#include <sys/types.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Signal numbers as defined in POSIX-2024 */
#define SIGHUP          1   /* Hangup */
#define SIGINT          2   /* Interrupt */
#define SIGQUIT         3   /* Quit */
#define SIGILL          4   /* Illegal instruction */
#define SIGTRAP         5   /* Trace/breakpoint trap */
#define SIGABRT         6   /* Abort */
#define SIGIOT          SIGABRT
#define SIGBUS          7   /* Bus error */
#define SIGFPE          8   /* Floating point exception */
#define SIGKILL         9   /* Kill (cannot be caught or ignored) */
#define SIGUSR1         10  /* User-defined signal 1 */
#define SIGSEGV         11  /* Segmentation violation */
#define SIGUSR2         12  /* User-defined signal 2 */
#define SIGPIPE         13  /* Broken pipe */
#define SIGALRM         14  /* Alarm clock */
#define SIGTERM         15  /* Termination */
#define SIGSTKFLT       16  /* Stack fault */
#define SIGCHLD         17  /* Child status changed */
#define SIGCONT         18  /* Continue */
#define SIGSTOP         19  /* Stop (cannot be caught or ignored) */
#define SIGTSTP         20  /* Keyboard stop */
#define SIGTTIN         21  /* Background read from tty */
#define SIGTTOU         22  /* Background write to tty */
#define SIGURG          23  /* Urgent condition on socket */
#define SIGXCPU         24  /* CPU limit exceeded */
#define SIGXFSZ         25  /* File size limit exceeded */
#define SIGVTALRM       26  /* Virtual alarm clock */
#define SIGPROF         27  /* Profiling alarm clock */
#define SIGWINCH        28  /* Window size change */
#define SIGIO           29  /* I/O now possible */
#define SIGPOLL         SIGIO
#define SIGPWR          30  /* Power failure restart */
#define SIGSYS          31  /* Bad system call */
#define SIGUNUSED       31

#define _NSIG           64  /* Biggest signal number + 1 */
#define NSIG            _NSIG

/* Signal stack size */
#define SIGSTKSZ        8192

/* Signal handling constants */
#define SIG_DFL         ((void (*)(int))0)     /* Default action */
#define SIG_IGN         ((void (*)(int))1)     /* Ignore signal */
#define SIG_ERR         ((void (*)(int))-1)    /* Error return */

/* sigprocmask() constants */
#define SIG_BLOCK       0   /* Block signals */
#define SIG_UNBLOCK     1   /* Unblock signals */
#define SIG_SETMASK     2   /* Set signal mask */

/* Signal set type */
typedef unsigned long sigset_t;

/* Signal information structure */
union sigval {
    int   sival_int;
    void *sival_ptr;
};

typedef struct {
    int      si_signo;    /* Signal number */
    int      si_errno;    /* Error number */
    int      si_code;     /* Signal code */
    pid_t    si_pid;      /* Sending process ID */
    uid_t    si_uid;      /* Real user ID of sending process */
    int      si_status;   /* Exit value or signal */
    clock_t  si_utime;    /* User time consumed */
    clock_t  si_stime;    /* System time consumed */
    union sigval si_value; /* Signal value */
    int      si_int;      /* POSIX.1b signal */
    void    *si_ptr;      /* POSIX.1b signal */
    int      si_overrun;  /* Timer overrun count */
    int      si_timerid;  /* Timer ID */
    void    *si_addr;     /* Memory location which caused fault */
    int      si_band;     /* Band event */
    int      si_fd;       /* File descriptor */
} siginfo_t;

/* Signal action structure */
struct sigaction {
    union {
        void (*sa_handler)(int);
        void (*sa_sigaction)(int, siginfo_t *, void *);
    };
    sigset_t   sa_mask;     /* Signals to be blocked during handler */
    int        sa_flags;    /* Signal action flags */
    void     (*sa_restorer)(void);  /* Obsolete - do not use */
};

/* sa_flags values */
#define SA_NOCLDSTOP    0x00000001  /* Don't send SIGCHLD when children stop */
#define SA_NOCLDWAIT    0x00000002  /* Don't create zombie on child death */
#define SA_SIGINFO      0x00000004  /* Invoke signal-catching function with three args */
#define SA_ONSTACK      0x08000000  /* Use signal stack by using sa_restorer */
#define SA_RESTART      0x10000000  /* Restart syscall on signal return */
#define SA_NODEFER      0x40000000  /* Don't automatically block the signal when handling */
#define SA_RESETHAND    0x80000000  /* Reset to SIG_DFL on entry to handler */

/* Signal stack */
typedef struct {
    void   *ss_sp;      /* Base address of stack */
    int     ss_flags;   /* Flags */
    size_t  ss_size;    /* Number of bytes in stack */
} stack_t;

/* ss_flags values */
#define SS_ONSTACK      1   /* Process is executing on alternate stack */
#define SS_DISABLE      2   /* Alternate stack is disabled */

/* POSIX-2024 signal functions */

/* Basic signal functions */
void (*signal(int sig, void (*func)(int)))(int);
int raise(int sig);

/* Advanced signal handling */
int sigaction(int sig, const struct sigaction *act, struct sigaction *oldact);
int sigprocmask(int how, const sigset_t *set, sigset_t *oldset);
int sigpending(sigset_t *set);
int sigsuspend(const sigset_t *mask);

/* Signal set manipulation */
int sigemptyset(sigset_t *set);
int sigfillset(sigset_t *set);
int sigaddset(sigset_t *set, int signum);
int sigdelset(sigset_t *set, int signum);
int sigismember(const sigset_t *set, int signum);

/* Real-time signals */
int sigqueue(pid_t pid, int sig, const union sigval value);
int sigtimedwait(const sigset_t *set, siginfo_t *info, const struct timespec *timeout);
int sigwaitinfo(const sigset_t *set, siginfo_t *info);
int sigwait(const sigset_t *set, int *sig);

/* Signal stack functions */
int sigaltstack(const stack_t *ss, stack_t *old_ss);

/* Process signaling */
int kill(pid_t pid, int sig);
int killpg(int pgrp, int sig);

/* Signal codes for si_code */
#define SI_USER         0   /* Sent by kill, sigsend or raise */
#define SI_KERNEL       0x80 /* Sent by the kernel from somewhere */
#define SI_QUEUE        -1  /* Sent by sigqueue */
#define SI_TIMER        -2  /* Sent by timer expiration */
#define SI_MESGQ        -3  /* Sent by real time mesq state change */
#define SI_ASYNCIO      -4  /* Sent by AIO completion */
#define SI_SIGIO        -5  /* Sent by queued SIGIO */
#define SI_TKILL        -6  /* Sent by tkill system call */

/* SIGILL si_code values */
#define ILL_ILLOPC      1   /* Illegal opcode */
#define ILL_ILLOPN      2   /* Illegal operand */
#define ILL_ILLADR      3   /* Illegal addressing mode */
#define ILL_ILLTRP      4   /* Illegal trap */
#define ILL_PRVOPC      5   /* Privileged opcode */
#define ILL_PRVREG      6   /* Privileged register */
#define ILL_COPROC      7   /* Coprocessor error */
#define ILL_BADSTK      8   /* Internal stack error */

/* SIGFPE si_code values */
#define FPE_INTDIV      1   /* Integer divide by zero */
#define FPE_INTOVF      2   /* Integer overflow */
#define FPE_FLTDIV      3   /* Floating point divide by zero */
#define FPE_FLTOVF      4   /* Floating point overflow */
#define FPE_FLTUND      5   /* Floating point underflow */
#define FPE_FLTRES      6   /* Floating point inexact result */
#define FPE_FLTINV      7   /* Floating point invalid operation */
#define FPE_FLTSUB      8   /* Subscript out of range */

/* SIGSEGV si_code values */
#define SEGV_MAPERR     1   /* Address not mapped to object */
#define SEGV_ACCERR     2   /* Invalid permissions for mapped object */

/* SIGBUS si_code values */
#define BUS_ADRALN      1   /* Invalid address alignment */
#define BUS_ADRERR      2   /* Non-existent physical address */
#define BUS_OBJERR      3   /* Object specific hardware error */

/* SIGTRAP si_code values */
#define TRAP_BRKPT      1   /* Process breakpoint */
#define TRAP_TRACE      2   /* Process trace trap */

/* SIGCHLD si_code values */
#define CLD_EXITED      1   /* Child has exited */
#define CLD_KILLED      2   /* Child was killed */
#define CLD_DUMPED      3   /* Child terminated abnormally */
#define CLD_TRAPPED     4   /* Traced child has trapped */
#define CLD_STOPPED     5   /* Child has stopped */
#define CLD_CONTINUED   6   /* Stopped child has continued */

/* SIGPOLL si_code values */
#define POLL_IN         1   /* Data input available */
#define POLL_OUT        2   /* Output buffers available */
#define POLL_MSG        3   /* Input message available */
#define POLL_ERR        4   /* I/O error */
#define POLL_PRI        5   /* High priority input available */
#define POLL_HUP        6   /* Device disconnected */

#ifdef __cplusplus
}
#endif

#endif /* _SIGNAL_H */