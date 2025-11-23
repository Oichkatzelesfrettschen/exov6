/**
 * @file linux_time.c
 * @brief Linux time and timer syscall implementations
 *
 * This file implements Linux time-related syscalls for the exokernel libOS:
 * - Clock operations (clock_gettime, clock_settime, clock_getres)
 * - Sleep operations (nanosleep, clock_nanosleep)
 * - Timer file descriptors (timerfd_create, timerfd_settime, timerfd_gettime)
 * - Legacy time functions (gettimeofday, settimeofday, time)
 * - Process timers (timer_create, timer_settime, timer_delete)
 */

#include "linux_syscall.h"
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* Forward declarations for exokernel primitives */
extern uint64_t exo_get_time_ns(void);
extern void exo_set_time_ns(uint64_t ns);
extern int exo_thread_yield(void);
extern void *exo_alloc_pages(size_t count);
extern void exo_free_pages(void *addr, size_t count);

/*============================================================================
 * Clock Types
 *============================================================================*/

#define CLOCK_REALTIME              0
#define CLOCK_MONOTONIC             1
#define CLOCK_PROCESS_CPUTIME_ID    2
#define CLOCK_THREAD_CPUTIME_ID     3
#define CLOCK_MONOTONIC_RAW         4
#define CLOCK_REALTIME_COARSE       5
#define CLOCK_MONOTONIC_COARSE      6
#define CLOCK_BOOTTIME              7
#define CLOCK_REALTIME_ALARM        8
#define CLOCK_BOOTTIME_ALARM        9
#define CLOCK_TAI                   11

/*============================================================================
 * Timer Constants
 *============================================================================*/

#define TIMER_ABSTIME               0x01

/* timerfd flags */
#define TFD_TIMER_ABSTIME           (1 << 0)
#define TFD_TIMER_CANCEL_ON_SET     (1 << 1)
#define TFD_CLOEXEC                 LINUX_O_CLOEXEC
#define TFD_NONBLOCK                LINUX_O_NONBLOCK

/* Timer notification */
#define SIGEV_SIGNAL                0
#define SIGEV_NONE                  1
#define SIGEV_THREAD                2
#define SIGEV_THREAD_ID             4

/*============================================================================
 * Time State
 *============================================================================*/

/* Boot time offset (nanoseconds since boot) */
static uint64_t boot_time_ns = 0;

/* Realtime offset (for settimeofday) */
static int64_t realtime_offset_ns = 0;

/* Monotonic start time */
static uint64_t monotonic_start_ns = 0;

/* TAI offset (currently just UTC) */
static int64_t tai_offset_sec = 37;  /* UTC-TAI offset as of 2024 */

/*============================================================================
 * Helper Functions
 *============================================================================*/

/**
 * Initialize time subsystem
 */
static void init_time(void)
{
    static bool initialized = false;
    if (!initialized) {
        monotonic_start_ns = exo_get_time_ns();
        boot_time_ns = monotonic_start_ns;
        initialized = true;
    }
}

/**
 * Convert nanoseconds to timespec
 */
static void ns_to_timespec(uint64_t ns, struct linux_timespec *ts)
{
    ts->tv_sec = ns / 1000000000ULL;
    ts->tv_nsec = ns % 1000000000ULL;
}

/**
 * Convert timespec to nanoseconds
 */
static uint64_t timespec_to_ns(const struct linux_timespec *ts)
{
    return (uint64_t)ts->tv_sec * 1000000000ULL + ts->tv_nsec;
}

/**
 * Validate timespec
 */
static int validate_timespec(const struct linux_timespec *ts)
{
    if (!ts) return -LINUX_EFAULT;
    if (ts->tv_nsec < 0 || ts->tv_nsec >= 1000000000LL) return -LINUX_EINVAL;
    return 0;
}

/*============================================================================
 * Clock Operations
 *============================================================================*/

/**
 * Get time from specified clock
 */
long linux_sys_clock_gettime(int clockid, struct linux_timespec *tp)
{
    init_time();

    if (!tp) {
        return -LINUX_EFAULT;
    }

    uint64_t now_ns = exo_get_time_ns();
    uint64_t result_ns;

    switch (clockid) {
    case CLOCK_REALTIME:
    case CLOCK_REALTIME_COARSE:
        result_ns = now_ns + realtime_offset_ns;
        break;

    case CLOCK_MONOTONIC:
    case CLOCK_MONOTONIC_RAW:
    case CLOCK_MONOTONIC_COARSE:
        result_ns = now_ns - monotonic_start_ns;
        break;

    case CLOCK_BOOTTIME:
    case CLOCK_BOOTTIME_ALARM:
        result_ns = now_ns - boot_time_ns;
        break;

    case CLOCK_PROCESS_CPUTIME_ID:
    case CLOCK_THREAD_CPUTIME_ID:
        /* TODO: Track actual CPU time */
        result_ns = now_ns - monotonic_start_ns;
        break;

    case CLOCK_TAI:
        result_ns = now_ns + realtime_offset_ns + (tai_offset_sec * 1000000000ULL);
        break;

    default:
        return -LINUX_EINVAL;
    }

    ns_to_timespec(result_ns, tp);
    return 0;
}

/**
 * Set time for specified clock
 */
long linux_sys_clock_settime(int clockid, const struct linux_timespec *tp)
{
    init_time();

    int ret = validate_timespec(tp);
    if (ret < 0) return ret;

    uint64_t now_ns = exo_get_time_ns();
    uint64_t target_ns = timespec_to_ns(tp);

    switch (clockid) {
    case CLOCK_REALTIME:
        realtime_offset_ns = (int64_t)target_ns - (int64_t)now_ns;
        return 0;

    case CLOCK_MONOTONIC:
    case CLOCK_MONOTONIC_RAW:
    case CLOCK_BOOTTIME:
        /* Cannot set monotonic clocks */
        return -LINUX_EPERM;

    default:
        return -LINUX_EINVAL;
    }
}

/**
 * Get clock resolution
 */
long linux_sys_clock_getres(int clockid, struct linux_timespec *res)
{
    if (!res) {
        return -LINUX_EFAULT;
    }

    switch (clockid) {
    case CLOCK_REALTIME:
    case CLOCK_MONOTONIC:
    case CLOCK_MONOTONIC_RAW:
    case CLOCK_BOOTTIME:
    case CLOCK_PROCESS_CPUTIME_ID:
    case CLOCK_THREAD_CPUTIME_ID:
    case CLOCK_TAI:
        /* Nanosecond resolution */
        res->tv_sec = 0;
        res->tv_nsec = 1;
        return 0;

    case CLOCK_REALTIME_COARSE:
    case CLOCK_MONOTONIC_COARSE:
        /* Coarse clocks have ~4ms resolution */
        res->tv_sec = 0;
        res->tv_nsec = 4000000;  /* 4ms */
        return 0;

    default:
        return -LINUX_EINVAL;
    }
}

/*============================================================================
 * Sleep Operations
 *============================================================================*/

/**
 * High-resolution sleep
 */
long linux_sys_nanosleep(const struct linux_timespec *req,
                         struct linux_timespec *rem)
{
    init_time();

    int ret = validate_timespec(req);
    if (ret < 0) return ret;

    uint64_t sleep_ns = timespec_to_ns(req);
    uint64_t start_ns = exo_get_time_ns();
    uint64_t end_ns = start_ns + sleep_ns;

    /* Busy-wait with yields for now */
    /* TODO: Proper blocking sleep with timer interrupt */
    while (exo_get_time_ns() < end_ns) {
        exo_thread_yield();
    }

    if (rem) {
        rem->tv_sec = 0;
        rem->tv_nsec = 0;
    }

    return 0;
}

/**
 * Sleep on specified clock
 */
long linux_sys_clock_nanosleep(int clockid, int flags,
                               const struct linux_timespec *req,
                               struct linux_timespec *rem)
{
    init_time();

    int ret = validate_timespec(req);
    if (ret < 0) return ret;

    uint64_t now_ns;
    uint64_t end_ns;

    /* Get current time on specified clock */
    struct linux_timespec current;
    ret = linux_sys_clock_gettime(clockid, &current);
    if (ret < 0) return ret;

    now_ns = timespec_to_ns(&current);

    if (flags & TIMER_ABSTIME) {
        /* Absolute time */
        end_ns = timespec_to_ns(req);
        if (end_ns <= now_ns) {
            return 0;  /* Already past */
        }
    } else {
        /* Relative time */
        end_ns = now_ns + timespec_to_ns(req);
    }

    uint64_t sleep_ns = end_ns - now_ns;

    /* Perform sleep */
    struct linux_timespec sleep_req;
    ns_to_timespec(sleep_ns, &sleep_req);
    return linux_sys_nanosleep(&sleep_req, rem);
}

/*============================================================================
 * Legacy Time Functions
 *============================================================================*/

/**
 * Get current time
 */
long linux_sys_time(int64_t *tloc)
{
    init_time();

    struct linux_timespec ts;
    linux_sys_clock_gettime(CLOCK_REALTIME, &ts);

    if (tloc) {
        *tloc = ts.tv_sec;
    }

    return ts.tv_sec;
}

/**
 * Get time of day
 */
long linux_sys_gettimeofday(struct linux_timeval *tv, void *tz)
{
    init_time();

    if (tv) {
        struct linux_timespec ts;
        linux_sys_clock_gettime(CLOCK_REALTIME, &ts);
        tv->tv_sec = ts.tv_sec;
        tv->tv_usec = ts.tv_nsec / 1000;
    }

    /* tz is obsolete and ignored */
    (void)tz;

    return 0;
}

/**
 * Set time of day
 */
long linux_sys_settimeofday(const struct linux_timeval *tv, const void *tz)
{
    init_time();

    if (tv) {
        struct linux_timespec ts;
        ts.tv_sec = tv->tv_sec;
        ts.tv_nsec = tv->tv_usec * 1000;
        return linux_sys_clock_settime(CLOCK_REALTIME, &ts);
    }

    (void)tz;
    return 0;
}

/**
 * Adjust system clock
 */
long linux_sys_adjtimex(void *buf)
{
    /* TODO: Implement NTP-style clock adjustment */
    (void)buf;
    return 0;
}

/*============================================================================
 * Timer File Descriptors (timerfd)
 *============================================================================*/

/**
 * Timer fd state
 */
struct timerfd {
    int clockid;                    /* Clock to use */
    uint64_t expiration_ns;         /* Next expiration time */
    uint64_t interval_ns;           /* Interval for periodic timer */
    uint64_t expirations;           /* Number of expirations since last read */
    bool armed;                     /* Is timer armed */
    bool abstime;                   /* Is expiration absolute */
    int flags;                      /* Creation flags */
};

/* Timer fd table */
#define TIMERFD_MAX 256
static struct timerfd timerfds[TIMERFD_MAX];
static int timerfd_next_id = 1;

/**
 * Create a timer file descriptor
 */
long linux_sys_timerfd_create(int clockid, int flags)
{
    init_time();

    /* Validate clockid */
    switch (clockid) {
    case CLOCK_REALTIME:
    case CLOCK_MONOTONIC:
    case CLOCK_BOOTTIME:
    case CLOCK_REALTIME_ALARM:
    case CLOCK_BOOTTIME_ALARM:
        break;
    default:
        return -LINUX_EINVAL;
    }

    /* Find free slot */
    int fd = -1;
    for (int i = 0; i < TIMERFD_MAX; i++) {
        if (timerfds[i].clockid == 0) {
            fd = i + 1000;  /* Offset to avoid collision with regular fds */
            timerfds[i].clockid = clockid;
            timerfds[i].flags = flags;
            timerfds[i].armed = false;
            timerfds[i].expiration_ns = 0;
            timerfds[i].interval_ns = 0;
            timerfds[i].expirations = 0;
            break;
        }
    }

    if (fd < 0) {
        return -LINUX_EMFILE;
    }

    return fd;
}

/**
 * timerfd itimerspec structure
 */
struct itimerspec {
    struct linux_timespec it_interval;  /* Timer interval */
    struct linux_timespec it_value;     /* Initial expiration */
};

/**
 * Arm or disarm timer
 */
long linux_sys_timerfd_settime(int fd, int flags,
                               const struct itimerspec *new_value,
                               struct itimerspec *old_value)
{
    init_time();

    if (fd < 1000 || fd >= 1000 + TIMERFD_MAX) {
        return -LINUX_EBADF;
    }

    struct timerfd *tfd = &timerfds[fd - 1000];
    if (tfd->clockid == 0) {
        return -LINUX_EBADF;
    }

    if (!new_value) {
        return -LINUX_EFAULT;
    }

    /* Return old value */
    if (old_value) {
        if (tfd->armed) {
            ns_to_timespec(tfd->expiration_ns, &old_value->it_value);
            ns_to_timespec(tfd->interval_ns, &old_value->it_interval);
        } else {
            old_value->it_value.tv_sec = 0;
            old_value->it_value.tv_nsec = 0;
            old_value->it_interval.tv_sec = 0;
            old_value->it_interval.tv_nsec = 0;
        }
    }

    /* Disarm if value is zero */
    if (new_value->it_value.tv_sec == 0 && new_value->it_value.tv_nsec == 0) {
        tfd->armed = false;
        tfd->expirations = 0;
        return 0;
    }

    /* Set new timer */
    uint64_t value_ns = timespec_to_ns(&new_value->it_value);
    uint64_t interval_ns = timespec_to_ns(&new_value->it_interval);

    if (flags & TFD_TIMER_ABSTIME) {
        tfd->expiration_ns = value_ns;
        tfd->abstime = true;
    } else {
        struct linux_timespec now;
        linux_sys_clock_gettime(tfd->clockid, &now);
        tfd->expiration_ns = timespec_to_ns(&now) + value_ns;
        tfd->abstime = false;
    }

    tfd->interval_ns = interval_ns;
    tfd->armed = true;
    tfd->expirations = 0;

    return 0;
}

/**
 * Get current timer setting
 */
long linux_sys_timerfd_gettime(int fd, struct itimerspec *curr_value)
{
    init_time();

    if (fd < 1000 || fd >= 1000 + TIMERFD_MAX) {
        return -LINUX_EBADF;
    }

    struct timerfd *tfd = &timerfds[fd - 1000];
    if (tfd->clockid == 0) {
        return -LINUX_EBADF;
    }

    if (!curr_value) {
        return -LINUX_EFAULT;
    }

    if (tfd->armed) {
        struct linux_timespec now;
        linux_sys_clock_gettime(tfd->clockid, &now);
        uint64_t now_ns = timespec_to_ns(&now);

        if (tfd->expiration_ns > now_ns) {
            ns_to_timespec(tfd->expiration_ns - now_ns, &curr_value->it_value);
        } else {
            curr_value->it_value.tv_sec = 0;
            curr_value->it_value.tv_nsec = 0;
        }
        ns_to_timespec(tfd->interval_ns, &curr_value->it_interval);
    } else {
        curr_value->it_value.tv_sec = 0;
        curr_value->it_value.tv_nsec = 0;
        curr_value->it_interval.tv_sec = 0;
        curr_value->it_interval.tv_nsec = 0;
    }

    return 0;
}

/**
 * Read timerfd (returns expiration count)
 */
long linux_sys_timerfd_read(int fd, uint64_t *expirations)
{
    init_time();

    if (fd < 1000 || fd >= 1000 + TIMERFD_MAX) {
        return -LINUX_EBADF;
    }

    struct timerfd *tfd = &timerfds[fd - 1000];
    if (tfd->clockid == 0) {
        return -LINUX_EBADF;
    }

    /* Check for expirations */
    if (tfd->armed) {
        struct linux_timespec now;
        linux_sys_clock_gettime(tfd->clockid, &now);
        uint64_t now_ns = timespec_to_ns(&now);

        while (tfd->expiration_ns <= now_ns) {
            tfd->expirations++;
            if (tfd->interval_ns > 0) {
                tfd->expiration_ns += tfd->interval_ns;
            } else {
                tfd->armed = false;
                break;
            }
        }
    }

    if (tfd->expirations == 0) {
        if (tfd->flags & TFD_NONBLOCK) {
            return -LINUX_EAGAIN;
        }
        /* Would block - should wait */
    }

    *expirations = tfd->expirations;
    tfd->expirations = 0;

    return sizeof(uint64_t);
}

/*============================================================================
 * POSIX Timers (timer_create, timer_settime, etc.)
 *============================================================================*/

/**
 * Signal event specification
 */
struct sigevent {
    int sigev_notify;               /* Notification method */
    int sigev_signo;                /* Signal number */
    union {
        int sival_int;
        void *sival_ptr;
    } sigev_value;
    void (*sigev_notify_function)(union { int; void*; });
    void *sigev_notify_attributes;
    int sigev_notify_thread_id;
};

/**
 * POSIX timer state
 */
struct posix_timer {
    int id;
    int clockid;
    struct sigevent sev;
    uint64_t expiration_ns;
    uint64_t interval_ns;
    bool armed;
    int overrun;
};

/* POSIX timer table */
#define POSIX_TIMER_MAX 256
static struct posix_timer posix_timers[POSIX_TIMER_MAX];
static int posix_timer_next_id = 1;

/**
 * Create a POSIX timer
 */
long linux_sys_timer_create(int clockid, struct sigevent *sevp, int *timerid)
{
    init_time();

    /* Validate clockid */
    switch (clockid) {
    case CLOCK_REALTIME:
    case CLOCK_MONOTONIC:
    case CLOCK_PROCESS_CPUTIME_ID:
    case CLOCK_THREAD_CPUTIME_ID:
    case CLOCK_BOOTTIME:
        break;
    default:
        return -LINUX_EINVAL;
    }

    if (!timerid) {
        return -LINUX_EFAULT;
    }

    /* Find free slot */
    int id = -1;
    for (int i = 0; i < POSIX_TIMER_MAX; i++) {
        if (posix_timers[i].id == 0) {
            id = posix_timer_next_id++;
            posix_timers[i].id = id;
            posix_timers[i].clockid = clockid;
            posix_timers[i].armed = false;
            posix_timers[i].overrun = 0;
            if (sevp) {
                posix_timers[i].sev = *sevp;
            } else {
                /* Default: SIGEV_SIGNAL with SIGALRM */
                posix_timers[i].sev.sigev_notify = SIGEV_SIGNAL;
                posix_timers[i].sev.sigev_signo = LINUX_SIGALRM;
            }
            break;
        }
    }

    if (id < 0) {
        return -LINUX_EAGAIN;
    }

    *timerid = id;
    return 0;
}

/**
 * Find POSIX timer by ID
 */
static struct posix_timer *find_posix_timer(int timerid)
{
    for (int i = 0; i < POSIX_TIMER_MAX; i++) {
        if (posix_timers[i].id == timerid) {
            return &posix_timers[i];
        }
    }
    return NULL;
}

/**
 * Arm or disarm a POSIX timer
 */
long linux_sys_timer_settime(int timerid, int flags,
                             const struct itimerspec *new_value,
                             struct itimerspec *old_value)
{
    init_time();

    struct posix_timer *timer = find_posix_timer(timerid);
    if (!timer) {
        return -LINUX_EINVAL;
    }

    if (!new_value) {
        return -LINUX_EFAULT;
    }

    /* Return old value */
    if (old_value) {
        if (timer->armed) {
            ns_to_timespec(timer->expiration_ns, &old_value->it_value);
            ns_to_timespec(timer->interval_ns, &old_value->it_interval);
        } else {
            old_value->it_value.tv_sec = 0;
            old_value->it_value.tv_nsec = 0;
            old_value->it_interval.tv_sec = 0;
            old_value->it_interval.tv_nsec = 0;
        }
    }

    /* Disarm if value is zero */
    if (new_value->it_value.tv_sec == 0 && new_value->it_value.tv_nsec == 0) {
        timer->armed = false;
        return 0;
    }

    /* Set timer */
    uint64_t value_ns = timespec_to_ns(&new_value->it_value);
    uint64_t interval_ns = timespec_to_ns(&new_value->it_interval);

    if (flags & TIMER_ABSTIME) {
        timer->expiration_ns = value_ns;
    } else {
        struct linux_timespec now;
        linux_sys_clock_gettime(timer->clockid, &now);
        timer->expiration_ns = timespec_to_ns(&now) + value_ns;
    }

    timer->interval_ns = interval_ns;
    timer->armed = true;
    timer->overrun = 0;

    return 0;
}

/**
 * Get current timer setting
 */
long linux_sys_timer_gettime(int timerid, struct itimerspec *curr_value)
{
    init_time();

    struct posix_timer *timer = find_posix_timer(timerid);
    if (!timer) {
        return -LINUX_EINVAL;
    }

    if (!curr_value) {
        return -LINUX_EFAULT;
    }

    if (timer->armed) {
        struct linux_timespec now;
        linux_sys_clock_gettime(timer->clockid, &now);
        uint64_t now_ns = timespec_to_ns(&now);

        if (timer->expiration_ns > now_ns) {
            ns_to_timespec(timer->expiration_ns - now_ns, &curr_value->it_value);
        } else {
            curr_value->it_value.tv_sec = 0;
            curr_value->it_value.tv_nsec = 0;
        }
        ns_to_timespec(timer->interval_ns, &curr_value->it_interval);
    } else {
        curr_value->it_value.tv_sec = 0;
        curr_value->it_value.tv_nsec = 0;
        curr_value->it_interval.tv_sec = 0;
        curr_value->it_interval.tv_nsec = 0;
    }

    return 0;
}

/**
 * Get timer overrun count
 */
long linux_sys_timer_getoverrun(int timerid)
{
    struct posix_timer *timer = find_posix_timer(timerid);
    if (!timer) {
        return -LINUX_EINVAL;
    }

    return timer->overrun;
}

/**
 * Delete a POSIX timer
 */
long linux_sys_timer_delete(int timerid)
{
    struct posix_timer *timer = find_posix_timer(timerid);
    if (!timer) {
        return -LINUX_EINVAL;
    }

    timer->id = 0;
    timer->armed = false;

    return 0;
}

/*============================================================================
 * Miscellaneous Time Functions
 *============================================================================*/

/**
 * Get resource usage timings
 */
long linux_sys_times(void *buf)
{
    /* TODO: Implement process times */
    (void)buf;
    return exo_get_time_ns() / 10000000ULL;  /* Return clock ticks */
}

/**
 * Get process times
 */
long linux_sys_getrusage(int who, struct linux_rusage *usage)
{
    init_time();

    if (!usage) {
        return -LINUX_EFAULT;
    }

    /* TODO: Track actual resource usage */
    uint64_t now_ns = exo_get_time_ns() - monotonic_start_ns;

    usage->ru_utime.tv_sec = now_ns / 2000000000ULL;
    usage->ru_utime.tv_usec = (now_ns / 2000) % 1000000;
    usage->ru_stime.tv_sec = now_ns / 2000000000ULL;
    usage->ru_stime.tv_usec = (now_ns / 2000) % 1000000;
    usage->ru_maxrss = 0;
    usage->ru_minflt = 0;
    usage->ru_majflt = 0;
    usage->ru_nvcsw = 0;
    usage->ru_nivcsw = 0;

    (void)who;
    return 0;
}

/*============================================================================
 * Timer Tick Processing
 *============================================================================*/

/**
 * Process timer expirations (called periodically by kernel)
 */
int linux_process_timers(void)
{
    init_time();

    struct linux_timespec now;
    linux_sys_clock_gettime(CLOCK_REALTIME, &now);
    uint64_t now_ns = timespec_to_ns(&now);

    int expired = 0;

    /* Check POSIX timers */
    for (int i = 0; i < POSIX_TIMER_MAX; i++) {
        struct posix_timer *timer = &posix_timers[i];
        if (timer->id != 0 && timer->armed) {
            while (timer->expiration_ns <= now_ns) {
                expired++;
                timer->overrun++;

                /* TODO: Deliver signal based on sigevent */

                if (timer->interval_ns > 0) {
                    timer->expiration_ns += timer->interval_ns;
                } else {
                    timer->armed = false;
                    break;
                }
            }
        }
    }

    /* Check timer file descriptors */
    for (int i = 0; i < TIMERFD_MAX; i++) {
        struct timerfd *tfd = &timerfds[i];
        if (tfd->clockid != 0 && tfd->armed) {
            struct linux_timespec clock_now;
            linux_sys_clock_gettime(tfd->clockid, &clock_now);
            uint64_t clock_ns = timespec_to_ns(&clock_now);

            while (tfd->expiration_ns <= clock_ns) {
                expired++;
                tfd->expirations++;

                if (tfd->interval_ns > 0) {
                    tfd->expiration_ns += tfd->interval_ns;
                } else {
                    tfd->armed = false;
                    break;
                }
            }
        }
    }

    return expired;
}

/*============================================================================
 * Debugging Interface
 *============================================================================*/

/**
 * Get time subsystem info
 */
int linux_get_time_info(uint64_t *uptime_ns, int *active_timers)
{
    init_time();

    if (uptime_ns) {
        *uptime_ns = exo_get_time_ns() - boot_time_ns;
    }

    if (active_timers) {
        int count = 0;
        for (int i = 0; i < POSIX_TIMER_MAX; i++) {
            if (posix_timers[i].id != 0 && posix_timers[i].armed) {
                count++;
            }
        }
        for (int i = 0; i < TIMERFD_MAX; i++) {
            if (timerfds[i].clockid != 0 && timerfds[i].armed) {
                count++;
            }
        }
        *active_timers = count;
    }

    return 0;
}
