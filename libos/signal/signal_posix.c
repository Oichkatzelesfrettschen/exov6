/* signal_posix.c - POSIX-2024 Compliant Signal Implementation */
#include <signal.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include "exo.h"

/* Signal state management */
typedef struct {
    struct sigaction actions[_NSIG];
    sigset_t blocked;
    sigset_t pending;
    stack_t alt_stack;
    int alt_stack_enabled;
} signal_state_t;

static _Thread_local signal_state_t sig_state = {0};
static _Thread_local int signal_initialized = 0;

/* Initialize signal state if not already done */
static void ensure_signal_init(void) {
    if (!signal_initialized) {
        memset(&sig_state, 0, sizeof(sig_state));
        /* Set default handlers */
        for (int i = 1; i < _NSIG; i++) {
            sig_state.actions[i].sa_handler = SIG_DFL;
        }
        signal_initialized = 1;
    }
}

/* Check if signal number is valid */
static int valid_signal(int sig) {
    return (sig > 0 && sig < _NSIG && sig != SIGKILL && sig != SIGSTOP);
}

/* POSIX signal() function - simplified interface */
void (*signal(int sig, void (*func)(int)))(int) {
    struct sigaction act, oldact;
    
    if (!valid_signal(sig)) {
        errno = EINVAL;
        return SIG_ERR;
    }
    
    act.sa_handler = func;
    sigemptyset(&act.sa_mask);
    act.sa_flags = SA_RESTART;
    
    if (sigaction(sig, &act, &oldact) < 0) {
        return SIG_ERR;
    }
    
    return oldact.sa_handler;
}

/* POSIX sigaction() function */
int sigaction(int sig, const struct sigaction *act, struct sigaction *oldact) {
    ensure_signal_init();
    
    if (!valid_signal(sig)) {
        errno = EINVAL;
        return -1;
    }
    
    if (oldact) {
        *oldact = sig_state.actions[sig];
    }
    
    if (act) {
        sig_state.actions[sig] = *act;
        /* SIGKILL and SIGSTOP cannot be caught or ignored */
        if (sig == SIGKILL || sig == SIGSTOP) {
            sig_state.actions[sig].sa_handler = SIG_DFL;
        }
    }
    
    return 0;
}

/* Signal set manipulation functions */
int sigemptyset(sigset_t *set) {
    if (!set) {
        errno = EINVAL;
        return -1;
    }
    *set = 0;
    return 0;
}

int sigfillset(sigset_t *set) {
    if (!set) {
        errno = EINVAL;
        return -1;
    }
    *set = ~0UL;
    return 0;
}

int sigaddset(sigset_t *set, int signum) {
    if (!set || signum <= 0 || signum >= _NSIG) {
        errno = EINVAL;
        return -1;
    }
    *set |= (1UL << signum);
    return 0;
}

int sigdelset(sigset_t *set, int signum) {
    if (!set || signum <= 0 || signum >= _NSIG) {
        errno = EINVAL;
        return -1;
    }
    *set &= ~(1UL << signum);
    return 0;
}

int sigismember(const sigset_t *set, int signum) {
    if (!set || signum <= 0 || signum >= _NSIG) {
        errno = EINVAL;
        return -1;
    }
    return (*set & (1UL << signum)) != 0;
}

/* Signal mask manipulation */
int sigprocmask(int how, const sigset_t *set, sigset_t *oldset) {
    ensure_signal_init();
    
    if (oldset) {
        *oldset = sig_state.blocked;
    }
    
    if (!set) {
        return 0;  /* Just return current mask */
    }
    
    switch (how) {
    case SIG_BLOCK:
        sig_state.blocked |= *set;
        break;
    case SIG_UNBLOCK:
        sig_state.blocked &= ~(*set);
        break;
    case SIG_SETMASK:
        sig_state.blocked = *set;
        break;
    default:
        errno = EINVAL;
        return -1;
    }
    
    /* SIGKILL and SIGSTOP cannot be blocked */
    sig_state.blocked &= ~((1UL << SIGKILL) | (1UL << SIGSTOP));
    
    return 0;
}

/* Get pending signals */
int sigpending(sigset_t *set) {
    if (!set) {
        errno = EINVAL;
        return -1;
    }
    
    ensure_signal_init();
    *set = sig_state.pending & sig_state.blocked;
    return 0;
}

/* Suspend execution until signal */
int sigsuspend(const sigset_t *mask) {
    sigset_t oldmask;
    
    ensure_signal_init();
    
    /* Temporarily replace signal mask */
    oldmask = sig_state.blocked;
    sig_state.blocked = *mask;
    sig_state.blocked &= ~((1UL << SIGKILL) | (1UL << SIGSTOP));
    
    /* Wait for signal - use exokernel yield */
    while (!(sig_state.pending & ~sig_state.blocked)) {
        exo_yield_to(0);  /* Yield to any process */
        /* Check for signals via exokernel */
        int pending = sigcheck();  /* From existing kernel interface */
        sig_state.pending |= pending;
    }
    
    /* Restore original mask */
    sig_state.blocked = oldmask;
    
    errno = EINTR;
    return -1;  /* sigsuspend always returns -1 with EINTR */
}

/* Send signal to process */
int kill(pid_t pid, int sig) {
    if (sig < 0 || sig >= _NSIG) {
        errno = EINVAL;
        return -1;
    }
    
    if (sig == 0) {
        /* Just check if process exists */
        return sigsend(pid, 0);  /* Use existing kernel interface */
    }
    
    return sigsend(pid, sig);  /* Use existing kernel interface */
}

/* Send signal to process group */
int killpg(int pgrp, int sig) {
    if (pgrp < 0) {
        errno = EINVAL;
        return -1;
    }
    
    return kill(-pgrp, sig);  /* Negative PID means process group */
}

/* Raise signal to current process */
int raise(int sig) {
    return kill(getpid(), sig);
}

/* Signal queue functions for real-time signals */
int sigqueue(pid_t pid, int sig, const union sigval value) {
    /* For now, just use regular kill - can be enhanced later */
    (void)value;  /* Unused for now */
    return kill(pid, sig);
}

/* Wait for signals with timeout */
int sigtimedwait(const sigset_t *set, siginfo_t *info, const struct timespec *timeout) {
    ensure_signal_init();
    
    /* Simplified implementation - check if any signals in set are pending */
    int pending_signals = sig_state.pending & *set & ~sig_state.blocked;
    
    if (pending_signals) {
        /* Find first pending signal */
        for (int sig = 1; sig < _NSIG; sig++) {
            if (pending_signals & (1UL << sig)) {
                sig_state.pending &= ~(1UL << sig);  /* Remove from pending */
                
                if (info) {
                    memset(info, 0, sizeof(*info));
                    info->si_signo = sig;
                    info->si_code = SI_USER;
                    info->si_pid = getpid();
                }
                
                return sig;
            }
        }
    }
    
    /* No signals pending - would normally wait with timeout */
    (void)timeout;  /* TODO: Implement timeout */
    errno = EAGAIN;
    return -1;
}

/* Wait for signals without timeout */
int sigwaitinfo(const sigset_t *set, siginfo_t *info) {
    return sigtimedwait(set, info, NULL);
}

/* Simple signal wait */
int sigwait(const sigset_t *set, int *sig) {
    siginfo_t info;
    int result = sigwaitinfo(set, &info);
    if (result > 0 && sig) {
        *sig = result;
        return 0;
    }
    return result < 0 ? errno : 0;
}

/* Alternate signal stack */
int sigaltstack(const stack_t *ss, stack_t *old_ss) {
    ensure_signal_init();
    
    if (old_ss) {
        *old_ss = sig_state.alt_stack;
        old_ss->ss_flags = sig_state.alt_stack_enabled ? 0 : SS_DISABLE;
    }
    
    if (ss) {
        if (ss->ss_flags & SS_DISABLE) {
            sig_state.alt_stack_enabled = 0;
        } else {
            if (ss->ss_size < SIGSTKSZ) {
                errno = ENOMEM;
                return -1;
            }
            sig_state.alt_stack = *ss;
            sig_state.alt_stack_enabled = 1;
        }
    }
    
    return 0;
}

/* Signal delivery function - called by kernel/interrupt handler */
void posix_signal_deliver(int sig, siginfo_t *info) {
    ensure_signal_init();
    
    if (sig <= 0 || sig >= _NSIG) {
        return;
    }
    
    /* Check if signal is blocked */
    if (sig_state.blocked & (1UL << sig)) {
        sig_state.pending |= (1UL << sig);
        return;
    }
    
    /* Get signal handler */
    struct sigaction *action = &sig_state.actions[sig];
    
    if (action->sa_handler == SIG_IGN) {
        return;  /* Ignore signal */
    }
    
    if (action->sa_handler == SIG_DFL) {
        /* Default action - for now just exit on most signals */
        switch (sig) {
        case SIGCHLD:
        case SIGURG:
        case SIGWINCH:
            /* Ignore by default */
            break;
        case SIGSTOP:
        case SIGTSTP:
        case SIGTTIN:
        case SIGTTOU:
            /* TODO: Stop process */
            break;
        case SIGCONT:
            /* TODO: Continue process */
            break;
        default:
            /* Terminate process */
            _exit(128 + sig);
        }
        return;
    }
    
    /* Call user handler */
    if (action->sa_flags & SA_SIGINFO) {
        /* Use sa_sigaction handler with siginfo */
        if (action->sa_sigaction && info) {
            action->sa_sigaction(sig, info, NULL);
        }
    } else {
        /* Use sa_handler */
        if (action->sa_handler) {
            action->sa_handler(sig);
        }
    }
    
    /* Reset handler if SA_RESETHAND flag is set */
    if (action->sa_flags & SA_RESETHAND) {
        action->sa_handler = SIG_DFL;
    }
}

/* Initialize signal system - called from libos init */
void posix_signal_init(void) {
    ensure_signal_init();
    
    /* Set up default signal handlers */
    struct sigaction act;
    act.sa_handler = SIG_DFL;
    sigemptyset(&act.sa_mask);
    act.sa_flags = 0;
    
    for (int i = 1; i < _NSIG; i++) {
        sigaction(i, &act, NULL);
    }
    
    /* Some signals are ignored by default */
    act.sa_handler = SIG_IGN;
    sigaction(SIGCHLD, &act, NULL);
    sigaction(SIGPIPE, &act, NULL);  /* Avoid broken pipe crashes */
}

/* Constants required by some applications */
const int SIGSTKSZ = 8192;  /* Minimum stack size for signal handler */
const int MINSIGSTKSZ = 2048;  /* Minimum stack size */