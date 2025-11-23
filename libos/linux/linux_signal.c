/**
 * @file linux_signal.c
 * @brief Linux signal syscall implementations
 *
 * This file implements Linux signal-related syscalls for the exokernel libOS.
 * Provides rt_sigaction, rt_sigprocmask, kill, and related signal handling.
 *
 * Signal Model:
 * - Per-thread signal masks and pending signals
 * - Thread group (process) level signal delivery
 * - Real-time signals with queuing
 * - Restartable system calls
 */

#include "linux_syscall.h"
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* Forward declarations */
extern int exo_thread_yield(void);
extern uint64_t exo_get_time_ns(void);

/*============================================================================
 * Signal Constants
 *============================================================================*/

/* Maximum number of standard signals */
#define LINUX_NSIG          64
#define LINUX_SIGSET_SIZE   (LINUX_NSIG / 8)  /* 8 bytes */

/* Real-time signal range */
#define LINUX_SIGRTMIN      32
#define LINUX_SIGRTMAX      64

/* Signal actions */
#define LINUX_SIG_DFL       ((void *)0)
#define LINUX_SIG_IGN       ((void *)1)
#define LINUX_SIG_ERR       ((void *)-1)

/* siginfo_t codes (si_code) */
#define LINUX_SI_USER       0   /* kill(), sigsend(), raise() */
#define LINUX_SI_KERNEL     128 /* Kernel */
#define LINUX_SI_QUEUE      -1  /* sigqueue() */
#define LINUX_SI_TIMER      -2  /* timer */
#define LINUX_SI_MESGQ      -3  /* message queue */
#define LINUX_SI_ASYNCIO    -4  /* async I/O */
#define LINUX_SI_SIGIO      -5  /* SIGIO */
#define LINUX_SI_TKILL      -6  /* tkill/tgkill */

/* SIGCHLD codes */
#define LINUX_CLD_EXITED    1
#define LINUX_CLD_KILLED    2
#define LINUX_CLD_DUMPED    3
#define LINUX_CLD_TRAPPED   4
#define LINUX_CLD_STOPPED   5
#define LINUX_CLD_CONTINUED 6

/*============================================================================
 * Signal Data Structures
 *============================================================================*/

/**
 * Signal set (64 signals, 1 bit each)
 */
typedef struct {
    unsigned long sig[LINUX_NSIG / (8 * sizeof(unsigned long))];
} linux_sigset_t;

/**
 * Signal information structure
 */
struct linux_siginfo {
    int si_signo;           /* Signal number */
    int si_errno;           /* Error number */
    int si_code;            /* Signal code */
    int _pad0;

    union {
        /* kill() */
        struct {
            int si_pid;     /* Sender PID */
            int si_uid;     /* Sender UID */
        } _kill;

        /* Timer */
        struct {
            int si_tid;     /* Timer ID */
            int si_overrun; /* Overrun count */
            int si_value;   /* Signal value */
        } _timer;

        /* SIGCHLD */
        struct {
            int si_pid;
            int si_uid;
            int si_status;
            long si_utime;
            long si_stime;
        } _sigchld;

        /* SIGILL, SIGFPE, SIGSEGV, SIGBUS */
        struct {
            void *si_addr;      /* Faulting address */
            short si_addr_lsb;  /* LSB of address */
        } _sigfault;

        /* SIGPOLL */
        struct {
            long si_band;
            int si_fd;
        } _sigpoll;

        /* Generic padding */
        char _pad[128 - 16];
    } _sifields;
};

/**
 * Signal action structure
 */
struct linux_sigaction_internal {
    void (*sa_handler)(int);                    /* Handler function */
    unsigned long sa_flags;                      /* Flags */
    void (*sa_restorer)(void);                   /* Restorer function */
    linux_sigset_t sa_mask;                      /* Blocked signals during handler */
};

/**
 * Pending signal queue entry
 */
struct linux_sigqueue {
    struct linux_sigqueue *next;
    struct linux_siginfo info;
};

/**
 * Per-thread signal state
 */
struct linux_signal_state {
    linux_sigset_t blocked;                      /* Blocked signals */
    linux_sigset_t pending;                      /* Pending signals (bitmap) */
    struct linux_sigqueue *queue;                /* Queued signals (for RT) */
    struct linux_sigaction_internal actions[LINUX_NSIG];  /* Signal actions */
    void *alt_stack;                             /* Alternate signal stack */
    size_t alt_stack_size;
    int in_signal;                               /* Currently handling signal */
    int last_signo;                              /* Last delivered signal */
};

/* Current thread's signal state */
static struct linux_signal_state *current_signals = NULL;

/*============================================================================
 * Signal Set Operations
 *============================================================================*/

/**
 * Initialize empty signal set
 */
static void sigemptyset_internal(linux_sigset_t *set)
{
    set->sig[0] = 0;
}

/**
 * Initialize full signal set
 */
static void sigfillset_internal(linux_sigset_t *set)
{
    set->sig[0] = ~0UL;
}

/**
 * Add signal to set
 */
static void sigaddset_internal(linux_sigset_t *set, int signo)
{
    if (signo >= 1 && signo <= LINUX_NSIG) {
        set->sig[0] |= (1UL << (signo - 1));
    }
}

/**
 * Remove signal from set
 */
static void sigdelset_internal(linux_sigset_t *set, int signo)
{
    if (signo >= 1 && signo <= LINUX_NSIG) {
        set->sig[0] &= ~(1UL << (signo - 1));
    }
}

/**
 * Test if signal is in set
 */
static int sigismember_internal(const linux_sigset_t *set, int signo)
{
    if (signo >= 1 && signo <= LINUX_NSIG) {
        return (set->sig[0] & (1UL << (signo - 1))) != 0;
    }
    return 0;
}

/**
 * Check if set is empty
 */
static int sigempty_internal(const linux_sigset_t *set)
{
    return set->sig[0] == 0;
}

/*============================================================================
 * Signal State Initialization
 *============================================================================*/

/**
 * Initialize signal state for current thread
 */
static void init_signal_state(void)
{
    static struct linux_signal_state state_storage;

    if (current_signals == NULL) {
        current_signals = &state_storage;

        sigemptyset_internal(&current_signals->blocked);
        sigemptyset_internal(&current_signals->pending);
        current_signals->queue = NULL;
        current_signals->alt_stack = NULL;
        current_signals->alt_stack_size = 0;
        current_signals->in_signal = 0;
        current_signals->last_signo = 0;

        /* Initialize all handlers to default */
        for (int i = 0; i < LINUX_NSIG; i++) {
            current_signals->actions[i].sa_handler = LINUX_SIG_DFL;
            current_signals->actions[i].sa_flags = 0;
            current_signals->actions[i].sa_restorer = NULL;
            sigemptyset_internal(&current_signals->actions[i].sa_mask);
        }
    }
}

/**
 * Get signal action for signal
 */
static struct linux_sigaction_internal *get_action(int signo)
{
    if (!current_signals) {
        init_signal_state();
    }

    if (signo < 1 || signo > LINUX_NSIG) {
        return NULL;
    }

    return &current_signals->actions[signo - 1];
}

/*============================================================================
 * rt_sigaction Implementation
 *============================================================================*/

/**
 * Examine and change signal action
 *
 * @param signo     Signal number
 * @param act       New action (or NULL)
 * @param oldact    Buffer for old action (or NULL)
 * @param sigsetsize Size of sigset_t (must be 8)
 */
long linux_sys_rt_sigaction(int signo, const struct linux_sigaction *act,
                            struct linux_sigaction *oldact, size_t sigsetsize)
{
    init_signal_state();

    /* Validate signal number */
    if (signo < 1 || signo > LINUX_NSIG) {
        return -LINUX_EINVAL;
    }

    /* Cannot change SIGKILL or SIGSTOP */
    if (signo == LINUX_SIGKILL || signo == LINUX_SIGSTOP) {
        return -LINUX_EINVAL;
    }

    /* Validate sigset size */
    if (sigsetsize != LINUX_SIGSET_SIZE) {
        return -LINUX_EINVAL;
    }

    struct linux_sigaction_internal *ka = get_action(signo);
    if (!ka) {
        return -LINUX_EINVAL;
    }

    /* Return old action */
    if (oldact) {
        oldact->sa_handler = ka->sa_handler;
        oldact->sa_flags = ka->sa_flags;
        oldact->sa_restorer = ka->sa_restorer;
        oldact->sa_mask = ka->sa_mask.sig[0];
    }

    /* Install new action */
    if (act) {
        ka->sa_handler = act->sa_handler;
        ka->sa_flags = act->sa_flags;
        ka->sa_restorer = act->sa_restorer;
        ka->sa_mask.sig[0] = act->sa_mask;

        /* SA_RESETHAND: reset to default after delivery */
        /* SA_NODEFER: don't block signal during handler */
        /* SA_RESTART: restart interrupted syscalls */
        /* SA_SIGINFO: handler takes 3 args */
    }

    return 0;
}

/*============================================================================
 * rt_sigprocmask Implementation
 *============================================================================*/

/**
 * Examine and change blocked signals
 *
 * @param how       How to modify mask (SIG_BLOCK, SIG_UNBLOCK, SIG_SETMASK)
 * @param set       New mask value
 * @param oldset    Buffer for old mask
 * @param sigsetsize Size of sigset_t
 */
long linux_sys_rt_sigprocmask(int how, const linux_sigset_t *set,
                              linux_sigset_t *oldset, size_t sigsetsize)
{
    init_signal_state();

    if (sigsetsize != LINUX_SIGSET_SIZE) {
        return -LINUX_EINVAL;
    }

    /* Return old mask */
    if (oldset) {
        *oldset = current_signals->blocked;
    }

    /* Modify mask */
    if (set) {
        switch (how) {
        case LINUX_SIG_BLOCK:
            current_signals->blocked.sig[0] |= set->sig[0];
            break;

        case LINUX_SIG_UNBLOCK:
            current_signals->blocked.sig[0] &= ~set->sig[0];
            break;

        case LINUX_SIG_SETMASK:
            current_signals->blocked.sig[0] = set->sig[0];
            break;

        default:
            return -LINUX_EINVAL;
        }

        /* Cannot block SIGKILL or SIGSTOP */
        sigdelset_internal(&current_signals->blocked, LINUX_SIGKILL);
        sigdelset_internal(&current_signals->blocked, LINUX_SIGSTOP);
    }

    return 0;
}

/*============================================================================
 * rt_sigpending Implementation
 *============================================================================*/

/**
 * Examine pending signals
 */
long linux_sys_rt_sigpending(linux_sigset_t *set, size_t sigsetsize)
{
    init_signal_state();

    if (sigsetsize != LINUX_SIGSET_SIZE) {
        return -LINUX_EINVAL;
    }

    if (!set) {
        return -LINUX_EFAULT;
    }

    *set = current_signals->pending;
    return 0;
}

/*============================================================================
 * rt_sigsuspend Implementation
 *============================================================================*/

/**
 * Wait for signal with temporary mask
 */
long linux_sys_rt_sigsuspend(const linux_sigset_t *mask, size_t sigsetsize)
{
    init_signal_state();

    if (sigsetsize != LINUX_SIGSET_SIZE) {
        return -LINUX_EINVAL;
    }

    /* Save current mask */
    linux_sigset_t saved = current_signals->blocked;

    /* Apply temporary mask */
    if (mask) {
        current_signals->blocked = *mask;
        sigdelset_internal(&current_signals->blocked, LINUX_SIGKILL);
        sigdelset_internal(&current_signals->blocked, LINUX_SIGSTOP);
    }

    /* Wait for signal */
    while (sigempty_internal(&current_signals->pending)) {
        exo_thread_yield();
    }

    /* Restore mask */
    current_signals->blocked = saved;

    /* Always returns -EINTR */
    return -LINUX_EINTR;
}

/*============================================================================
 * rt_sigtimedwait Implementation
 *============================================================================*/

/**
 * Wait for signal with timeout
 */
long linux_sys_rt_sigtimedwait(const linux_sigset_t *set,
                               struct linux_siginfo *info,
                               const struct linux_timespec *timeout,
                               size_t sigsetsize)
{
    init_signal_state();

    if (sigsetsize != LINUX_SIGSET_SIZE) {
        return -LINUX_EINVAL;
    }

    if (!set) {
        return -LINUX_EFAULT;
    }

    /* Calculate deadline */
    uint64_t deadline = 0;
    if (timeout) {
        uint64_t now = exo_get_time_ns();
        deadline = now + timeout->tv_sec * 1000000000ULL + timeout->tv_nsec;
    }

    /* Wait for one of the signals in set */
    while (1) {
        /* Check for pending signal in set */
        for (int signo = 1; signo <= LINUX_NSIG; signo++) {
            if (sigismember_internal(set, signo) &&
                sigismember_internal(&current_signals->pending, signo)) {
                /* Found a pending signal */
                sigdelset_internal(&current_signals->pending, signo);

                if (info) {
                    info->si_signo = signo;
                    info->si_errno = 0;
                    info->si_code = LINUX_SI_USER;
                }

                return signo;
            }
        }

        /* Check timeout */
        if (timeout) {
            uint64_t now = exo_get_time_ns();
            if (now >= deadline) {
                return -LINUX_EAGAIN;
            }
        }

        exo_thread_yield();
    }
}

/*============================================================================
 * rt_sigqueueinfo Implementation
 *============================================================================*/

/**
 * Queue signal with data
 */
long linux_sys_rt_sigqueueinfo(int pid, int signo, struct linux_siginfo *info)
{
    if (signo < 1 || signo > LINUX_NSIG) {
        return -LINUX_EINVAL;
    }

    /* Only SI_QUEUE is allowed for user processes */
    if (info && info->si_code != LINUX_SI_QUEUE) {
        return -LINUX_EPERM;
    }

    /* TODO: Send signal to target process */
    return linux_sys_kill(pid, signo);
}

/**
 * Queue signal to thread
 */
long linux_sys_rt_tgsigqueueinfo(int tgid, int tid, int signo,
                                 struct linux_siginfo *info)
{
    if (signo < 1 || signo > LINUX_NSIG) {
        return -LINUX_EINVAL;
    }

    /* TODO: Send signal to specific thread */
    return linux_sys_tgkill(tgid, tid, signo);
}

/*============================================================================
 * kill/tgkill/tkill Implementation
 *============================================================================*/

/**
 * Send signal to process
 */
long linux_sys_kill(int pid, int signo)
{
    init_signal_state();

    /* Validate signal */
    if (signo < 0 || signo > LINUX_NSIG) {
        return -LINUX_EINVAL;
    }

    /* Signal 0 is used to test if process exists */
    if (signo == 0) {
        /* TODO: Check if process exists */
        return 0;
    }

    /* For now, only support sending to self */
    /* TODO: Implement full process targeting */
    if (pid > 0) {
        /* Send to specific process */
        sigaddset_internal(&current_signals->pending, signo);
    } else if (pid == 0) {
        /* Send to process group */
        sigaddset_internal(&current_signals->pending, signo);
    } else if (pid == -1) {
        /* Send to all processes (except init) */
        sigaddset_internal(&current_signals->pending, signo);
    } else {
        /* Send to process group -pid */
        sigaddset_internal(&current_signals->pending, signo);
    }

    return 0;
}

/**
 * Send signal to thread in process
 */
long linux_sys_tgkill(int tgid, int tid, int signo)
{
    init_signal_state();

    if (signo < 0 || signo > LINUX_NSIG) {
        return -LINUX_EINVAL;
    }

    if (tid <= 0 || tgid <= 0) {
        return -LINUX_EINVAL;
    }

    if (signo == 0) {
        return 0;
    }

    /* TODO: Target specific thread */
    sigaddset_internal(&current_signals->pending, signo);
    return 0;
}

/**
 * Send signal to thread (obsolete)
 */
long linux_sys_tkill(int tid, int signo)
{
    /* tkill doesn't validate tgid, potential security issue */
    return linux_sys_tgkill(0, tid, signo);
}

/*============================================================================
 * pause Implementation
 *============================================================================*/

/**
 * Wait for signal
 */
long linux_sys_pause(void)
{
    init_signal_state();

    while (sigempty_internal(&current_signals->pending)) {
        exo_thread_yield();
    }

    return -LINUX_EINTR;
}

/*============================================================================
 * Alarm and Timer Implementation
 *============================================================================*/

/* Alarm state */
static uint64_t alarm_deadline = 0;

/**
 * Set alarm timer
 */
long linux_sys_alarm(unsigned int seconds)
{
    init_signal_state();

    uint64_t now = exo_get_time_ns();
    unsigned int remaining = 0;

    /* Calculate remaining time from previous alarm */
    if (alarm_deadline > now) {
        remaining = (alarm_deadline - now) / 1000000000ULL;
    }

    /* Set new alarm */
    if (seconds > 0) {
        alarm_deadline = now + (uint64_t)seconds * 1000000000ULL;
    } else {
        alarm_deadline = 0;
    }

    return remaining;
}

/**
 * Interval timer structure
 */
struct linux_itimerval {
    struct linux_timeval it_interval;  /* Timer interval */
    struct linux_timeval it_value;     /* Current value */
};

/* Timer state (simplified - one of each type) */
static struct linux_itimerval itimers[3];

/**
 * Set interval timer
 */
long linux_sys_setitimer(int which, const struct linux_itimerval *new_value,
                         struct linux_itimerval *old_value)
{
    if (which < 0 || which > 2) {
        return -LINUX_EINVAL;
    }

    if (old_value) {
        *old_value = itimers[which];
    }

    if (new_value) {
        itimers[which] = *new_value;
    }

    return 0;
}

/**
 * Get interval timer
 */
long linux_sys_getitimer(int which, struct linux_itimerval *curr_value)
{
    if (which < 0 || which > 2) {
        return -LINUX_EINVAL;
    }

    if (!curr_value) {
        return -LINUX_EFAULT;
    }

    *curr_value = itimers[which];
    return 0;
}

/*============================================================================
 * Alternate Signal Stack
 *============================================================================*/

/**
 * Signal stack structure
 */
struct linux_sigaltstack {
    void *ss_sp;        /* Stack base */
    int ss_flags;       /* Flags */
    size_t ss_size;     /* Stack size */
};

/**
 * Set alternate signal stack
 */
long linux_sys_sigaltstack(const struct linux_sigaltstack *ss,
                           struct linux_sigaltstack *old_ss)
{
    init_signal_state();

    /* Return old stack */
    if (old_ss) {
        old_ss->ss_sp = current_signals->alt_stack;
        old_ss->ss_size = current_signals->alt_stack_size;
        old_ss->ss_flags = current_signals->alt_stack ? 0 : LINUX_SS_DISABLE;
        if (current_signals->in_signal && current_signals->alt_stack) {
            old_ss->ss_flags |= LINUX_SS_ONSTACK;
        }
    }

    /* Set new stack */
    if (ss) {
        if (ss->ss_flags & LINUX_SS_DISABLE) {
            current_signals->alt_stack = NULL;
            current_signals->alt_stack_size = 0;
        } else {
            if (ss->ss_size < LINUX_MINSIGSTKSZ) {
                return -LINUX_ENOMEM;
            }
            current_signals->alt_stack = ss->ss_sp;
            current_signals->alt_stack_size = ss->ss_size;
        }
    }

    return 0;
}

/*============================================================================
 * signalfd Implementation
 *============================================================================*/

/**
 * Create file descriptor for signals
 */
long linux_sys_signalfd4(int fd, const linux_sigset_t *mask,
                         size_t sizemask, int flags)
{
    /* TODO: Implement signalfd */
    /* This creates a file descriptor that can be used with select/poll/epoll
     * to wait for signals instead of using signal handlers */
    return -LINUX_ENOSYS;
}

/**
 * signalfd (legacy)
 */
long linux_sys_signalfd(int fd, const linux_sigset_t *mask, size_t sizemask)
{
    return linux_sys_signalfd4(fd, mask, sizemask, 0);
}

/*============================================================================
 * Signal Delivery
 *============================================================================*/

/**
 * Check for and deliver pending signals
 * Called on return from syscall or interrupt
 */
int linux_deliver_signal(void)
{
    if (!current_signals) {
        return 0;
    }

    /* Check alarm */
    if (alarm_deadline > 0) {
        uint64_t now = exo_get_time_ns();
        if (now >= alarm_deadline) {
            alarm_deadline = 0;
            sigaddset_internal(&current_signals->pending, LINUX_SIGALRM);
        }
    }

    /* Find deliverable signal (pending and not blocked) */
    for (int signo = 1; signo <= LINUX_NSIG; signo++) {
        if (sigismember_internal(&current_signals->pending, signo) &&
            !sigismember_internal(&current_signals->blocked, signo)) {

            /* Clear pending */
            sigdelset_internal(&current_signals->pending, signo);

            struct linux_sigaction_internal *ka = get_action(signo);
            if (!ka) continue;

            /* Check action */
            if (ka->sa_handler == LINUX_SIG_IGN) {
                continue;  /* Ignored */
            }

            if (ka->sa_handler == LINUX_SIG_DFL) {
                /* Default action */
                switch (signo) {
                case LINUX_SIGCHLD:
                case LINUX_SIGURG:
                case LINUX_SIGWINCH:
                    /* Ignore by default */
                    continue;

                case LINUX_SIGSTOP:
                case LINUX_SIGTSTP:
                case LINUX_SIGTTIN:
                case LINUX_SIGTTOU:
                    /* Stop process */
                    /* TODO: Implement stop */
                    continue;

                case LINUX_SIGCONT:
                    /* Continue if stopped */
                    continue;

                default:
                    /* Terminate (possibly with core) */
                    /* TODO: Implement termination */
                    return signo;
                }
            }

            /* Call user handler */
            current_signals->in_signal = 1;
            current_signals->last_signo = signo;

            /* Block additional signals during handler */
            linux_sigset_t saved_mask = current_signals->blocked;
            current_signals->blocked.sig[0] |= ka->sa_mask.sig[0];
            if (!(ka->sa_flags & LINUX_SA_NODEFER)) {
                sigaddset_internal(&current_signals->blocked, signo);
            }

            /* Call handler */
            if (ka->sa_flags & LINUX_SA_SIGINFO) {
                /* Handler takes siginfo */
                void (*handler)(int, struct linux_siginfo *, void *) =
                    (void (*)(int, struct linux_siginfo *, void *))ka->sa_handler;
                struct linux_siginfo info = {
                    .si_signo = signo,
                    .si_errno = 0,
                    .si_code = LINUX_SI_USER
                };
                handler(signo, &info, NULL);
            } else {
                ka->sa_handler(signo);
            }

            /* Restore mask */
            current_signals->blocked = saved_mask;
            current_signals->in_signal = 0;

            /* SA_RESETHAND: reset to default */
            if (ka->sa_flags & LINUX_SA_RESETHAND) {
                ka->sa_handler = LINUX_SIG_DFL;
            }

            return signo;
        }
    }

    return 0;
}

/*============================================================================
 * Process Group / Session Signals
 *============================================================================*/

/**
 * Send signal to process group
 */
long linux_sys_killpg(int pgrp, int signo)
{
    if (pgrp <= 0) {
        return -LINUX_EINVAL;
    }
    return linux_sys_kill(-pgrp, signo);
}

/*============================================================================
 * Signal Return (for kernel use)
 *============================================================================*/

/**
 * Return from signal handler
 */
long linux_sys_rt_sigreturn(void)
{
    /* This is called by the signal trampoline (sa_restorer) */
    /* Restore the interrupted context */

    if (!current_signals) {
        return -LINUX_EFAULT;
    }

    current_signals->in_signal = 0;

    /* The actual return happens through context restoration */
    /* This syscall doesn't really return in the normal sense */
    return 0;
}

/*============================================================================
 * Debugging Interface
 *============================================================================*/

/**
 * Get signal state for debugging
 */
int linux_get_signal_info(int *pending_count, int *blocked_count)
{
    if (!current_signals) {
        if (pending_count) *pending_count = 0;
        if (blocked_count) *blocked_count = 0;
        return 0;
    }

    int pending = 0;
    int blocked = 0;

    for (int i = 1; i <= LINUX_NSIG; i++) {
        if (sigismember_internal(&current_signals->pending, i)) {
            pending++;
        }
        if (sigismember_internal(&current_signals->blocked, i)) {
            blocked++;
        }
    }

    if (pending_count) *pending_count = pending;
    if (blocked_count) *blocked_count = blocked;

    return 0;
}

/**
 * Get handler for signal
 */
void *linux_get_signal_handler(int signo)
{
    struct linux_sigaction_internal *ka = get_action(signo);
    if (!ka) {
        return LINUX_SIG_DFL;
    }
    return ka->sa_handler;
}
