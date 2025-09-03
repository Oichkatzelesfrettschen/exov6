/**
 * time.c - POSIX time functions for FeuerBird exokernel
 * 
 * Implements time(), clock_gettime(), nanosleep() and related functions
 * using exokernel timer capabilities.
 */

#include "types.h"
#include "defs.h"
#include "date.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include <arch.h>
#include "libos/posix.h"
#include "exo.h"
#include "errno.h"
#include <time.h>
#include <sys/time.h>
#include <signal.h>

// Time constants
#define NSEC_PER_SEC  1000000000L
#define USEC_PER_SEC  1000000L
#define NSEC_PER_USEC 1000L

// Timer state
typedef struct timer_state {
    exo_cap timer_cap;
    uint64_t boot_time;      // System boot time in nanoseconds
    uint64_t last_ticks;      // Last tick count
    int initialized;
} timer_state_t;

static timer_state_t timer_state = {0};

// Initialize timer subsystem
static int
init_timer(void)
{
    if (timer_state.initialized)
        return 0;
    
    // Request timer capability from exokernel
    timer_state.timer_cap = exo_request_timer();
    if (timer_state.timer_cap.id == 0) {
        errno = ENOSYS;
        return -1;
    }
    
    // Get boot time
    timer_state.boot_time = exo_get_boot_time(timer_state.timer_cap);
    timer_state.last_ticks = exo_get_ticks(timer_state.timer_cap);
    timer_state.initialized = 1;
    
    return 0;
}

// Get current time in nanoseconds since epoch
static uint64_t
get_time_ns(void)
{
    uint64_t ticks;
    uint64_t ns_per_tick;
    
    if (init_timer() < 0)
        return 0;
    
    // Get current tick count
    ticks = exo_get_ticks(timer_state.timer_cap);
    
    // Get nanoseconds per tick
    ns_per_tick = exo_get_tick_rate(timer_state.timer_cap);
    
    // Calculate time since boot
    uint64_t ns_since_boot = (ticks - timer_state.last_ticks) * ns_per_tick;
    
    // Add to boot time to get absolute time
    return timer_state.boot_time + ns_since_boot;
}

/**
 * time - Get current time
 * 
 * @t: Pointer to store time (or NULL)
 * 
 * Returns current time in seconds since epoch
 */
time_t
libos_time(time_t *t)
{
    uint64_t ns = get_time_ns();
    time_t seconds = ns / NSEC_PER_SEC;
    
    if (t != NULL)
        *t = seconds;
    
    return seconds;
}

/**
 * clock_gettime - Get time with nanosecond precision
 * 
 * @clk_id: Clock ID
 * @tp: Timespec to store result
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_clock_gettime(clockid_t clk_id, struct timespec *tp)
{
    uint64_t ns;
    
    if (tp == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    if (init_timer() < 0)
        return -1;
    
    switch (clk_id) {
    case CLOCK_REALTIME:
        // Wall-clock time
        ns = get_time_ns();
        tp->tv_sec = ns / NSEC_PER_SEC;
        tp->tv_nsec = ns % NSEC_PER_SEC;
        break;
        
    case CLOCK_MONOTONIC:
        // Monotonic time since boot
        ns = exo_get_monotonic_ns(timer_state.timer_cap);
        tp->tv_sec = ns / NSEC_PER_SEC;
        tp->tv_nsec = ns % NSEC_PER_SEC;
        break;
        
    case CLOCK_PROCESS_CPUTIME_ID:
        // Process CPU time
        ns = exo_get_process_time_ns(timer_state.timer_cap);
        tp->tv_sec = ns / NSEC_PER_SEC;
        tp->tv_nsec = ns % NSEC_PER_SEC;
        break;
        
    case CLOCK_THREAD_CPUTIME_ID:
        // Thread CPU time
        ns = exo_get_thread_time_ns(timer_state.timer_cap);
        tp->tv_sec = ns / NSEC_PER_SEC;
        tp->tv_nsec = ns % NSEC_PER_SEC;
        break;
        
    default:
        errno = EINVAL;
        return -1;
    }
    
    return 0;
}

/**
 * clock_settime - Set system time
 * 
 * @clk_id: Clock ID (must be CLOCK_REALTIME)
 * @tp: New time value
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_clock_settime(clockid_t clk_id, const struct timespec *tp)
{
    uint64_t new_ns;
    
    if (tp == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    if (clk_id != CLOCK_REALTIME) {
        errno = EINVAL;
        return -1;
    }
    
    if (init_timer() < 0)
        return -1;
    
    // Calculate new time in nanoseconds
    new_ns = (uint64_t)tp->tv_sec * NSEC_PER_SEC + tp->tv_nsec;
    
    // Set system time (requires privilege)
    if (exo_set_system_time(timer_state.timer_cap, new_ns) < 0) {
        errno = EPERM;
        return -1;
    }
    
    return 0;
}

/**
 * clock_getres - Get clock resolution
 * 
 * @clk_id: Clock ID
 * @res: Timespec to store resolution
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_clock_getres(clockid_t clk_id, struct timespec *res)
{
    uint64_t ns_per_tick;
    
    if (res == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    if (init_timer() < 0)
        return -1;
    
    switch (clk_id) {
    case CLOCK_REALTIME:
    case CLOCK_MONOTONIC:
    case CLOCK_PROCESS_CPUTIME_ID:
    case CLOCK_THREAD_CPUTIME_ID:
        // Get timer resolution
        ns_per_tick = exo_get_tick_rate(timer_state.timer_cap);
        res->tv_sec = 0;
        res->tv_nsec = ns_per_tick;
        break;
        
    default:
        errno = EINVAL;
        return -1;
    }
    
    return 0;
}

/**
 * nanosleep - High resolution sleep
 * 
 * @req: Requested sleep duration
 * @rem: Remaining time if interrupted (or NULL)
 * 
 * Returns 0 on success, -1 if interrupted
 */
int
libos_nanosleep(const struct timespec *req, struct timespec *rem)
{
    uint64_t sleep_ns;
    uint64_t start_ns, end_ns, elapsed_ns;
    
    if (req == NULL || req->tv_sec < 0 || req->tv_nsec < 0 ||
        req->tv_nsec >= NSEC_PER_SEC) {
        errno = EINVAL;
        return -1;
    }
    
    if (init_timer() < 0)
        return -1;
    
    // Calculate sleep duration in nanoseconds
    sleep_ns = (uint64_t)req->tv_sec * NSEC_PER_SEC + req->tv_nsec;
    
    // Get start time
    start_ns = exo_get_monotonic_ns(timer_state.timer_cap);
    
    // Request sleep from exokernel
    int result = exo_sleep_ns(timer_state.timer_cap, sleep_ns);
    
    if (result < 0) {
        // Sleep was interrupted
        end_ns = exo_get_monotonic_ns(timer_state.timer_cap);
        elapsed_ns = end_ns - start_ns;
        
        if (rem != NULL && elapsed_ns < sleep_ns) {
            // Calculate remaining time
            uint64_t remaining_ns = sleep_ns - elapsed_ns;
            rem->tv_sec = remaining_ns / NSEC_PER_SEC;
            rem->tv_nsec = remaining_ns % NSEC_PER_SEC;
        }
        
        errno = EINTR;
        return -1;
    }
    
    return 0;
}

/**
 * gettimeofday - Get current time
 * 
 * @tv: Timeval to store result
 * @tz: Timezone (ignored)
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_gettimeofday(struct timeval *tv, struct timezone *tz)
{
    uint64_t ns;
    
    if (tv == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    ns = get_time_ns();
    tv->tv_sec = ns / NSEC_PER_SEC;
    tv->tv_usec = (ns % NSEC_PER_SEC) / NSEC_PER_USEC;
    
    // Timezone not supported
    if (tz != NULL) {
        tz->tz_minuteswest = 0;
        tz->tz_dsttime = 0;
    }
    
    return 0;
}

/**
 * settimeofday - Set current time
 * 
 * @tv: New time value
 * @tz: Timezone (ignored)
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_settimeofday(const struct timeval *tv, const struct timezone *tz)
{
    struct timespec ts;
    
    if (tv == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    // Convert timeval to timespec
    ts.tv_sec = tv->tv_sec;
    ts.tv_nsec = tv->tv_usec * NSEC_PER_USEC;
    
    return libos_clock_settime(CLOCK_REALTIME, &ts);
}

/**
 * sleep - Sleep for specified seconds
 * 
 * @seconds: Number of seconds to sleep
 * 
 * Returns 0 if slept full duration, remaining seconds if interrupted
 */
unsigned int
libos_sleep(unsigned int seconds)
{
    struct timespec req, rem;
    
    req.tv_sec = seconds;
    req.tv_nsec = 0;
    
    if (libos_nanosleep(&req, &rem) < 0) {
        // Return remaining seconds
        return rem.tv_sec + (rem.tv_nsec > 0 ? 1 : 0);
    }
    
    return 0;
}

/**
 * usleep - Sleep for microseconds
 * 
 * @usec: Number of microseconds to sleep
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_usleep(useconds_t usec)
{
    struct timespec req;
    
    if (usec >= USEC_PER_SEC) {
        errno = EINVAL;
        return -1;
    }
    
    req.tv_sec = usec / USEC_PER_SEC;
    req.tv_nsec = (usec % USEC_PER_SEC) * NSEC_PER_USEC;
    
    return libos_nanosleep(&req, NULL);
}

/**
 * alarm - Set alarm signal
 * 
 * @seconds: Seconds until SIGALRM
 * 
 * Returns previous alarm time remaining
 */
unsigned int
libos_alarm(unsigned int seconds)
{
    static exo_cap alarm_cap = {0};
    unsigned int prev_alarm = 0;
    
    if (init_timer() < 0)
        return 0;
    
    // Cancel previous alarm and get remaining time
    if (alarm_cap.id != 0) {
        uint64_t remaining_ns = exo_cancel_timer(alarm_cap);
        prev_alarm = (remaining_ns + NSEC_PER_SEC - 1) / NSEC_PER_SEC;
        exo_release_capability(alarm_cap);
        alarm_cap.id = 0;
    }
    
    // Set new alarm if requested
    if (seconds > 0) {
        uint64_t alarm_ns = (uint64_t)seconds * NSEC_PER_SEC;
        alarm_cap = exo_set_timer(timer_state.timer_cap, alarm_ns, SIGALRM);
        if (alarm_cap.id == 0) {
            errno = EAGAIN;
            return prev_alarm;
        }
    }
    
    return prev_alarm;
}

/**
 * times - Get process times
 * 
 * @buf: Buffer to store times
 * 
 * Returns elapsed real time in clock ticks, or -1 on error
 */
clock_t
libos_times(struct tms *buf)
{
    uint64_t user_ns, system_ns, children_user_ns, children_system_ns;
    clock_t ticks_per_sec;
    
    if (buf == NULL) {
        errno = EINVAL;
        return (clock_t)-1;
    }
    
    if (init_timer() < 0)
        return (clock_t)-1;
    
    // Get process times from exokernel
    if (exo_get_process_times(timer_state.timer_cap,
                              &user_ns, &system_ns,
                              &children_user_ns, &children_system_ns) < 0) {
        errno = ESRCH;
        return (clock_t)-1;
    }
    
    // Get clock ticks per second
    ticks_per_sec = exo_get_clk_tck(timer_state.timer_cap);
    
    // Convert nanoseconds to clock ticks
    buf->tms_utime = (user_ns * ticks_per_sec) / NSEC_PER_SEC;
    buf->tms_stime = (system_ns * ticks_per_sec) / NSEC_PER_SEC;
    buf->tms_cutime = (children_user_ns * ticks_per_sec) / NSEC_PER_SEC;
    buf->tms_cstime = (children_system_ns * ticks_per_sec) / NSEC_PER_SEC;
    
    // Return elapsed real time since boot in clock ticks
    uint64_t elapsed_ns = exo_get_monotonic_ns(timer_state.timer_cap);
    return (elapsed_ns * ticks_per_sec) / NSEC_PER_SEC;
}

/**
 * getitimer - Get interval timer
 * 
 * @which: Timer type
 * @value: Buffer to store timer value
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_getitimer(int which, struct itimerval *value)
{
    exo_cap timer_cap;
    uint64_t remaining_ns, interval_ns;
    
    if (value == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    if (init_timer() < 0)
        return -1;
    
    // Get timer based on type
    switch (which) {
    case ITIMER_REAL:
        timer_cap = exo_get_itimer(timer_state.timer_cap, EXO_ITIMER_REAL);
        break;
    case ITIMER_VIRTUAL:
        timer_cap = exo_get_itimer(timer_state.timer_cap, EXO_ITIMER_VIRTUAL);
        break;
    case ITIMER_PROF:
        timer_cap = exo_get_itimer(timer_state.timer_cap, EXO_ITIMER_PROF);
        break;
    default:
        errno = EINVAL;
        return -1;
    }
    
    if (timer_cap.id == 0) {
        // No timer set
        value->it_value.tv_sec = 0;
        value->it_value.tv_usec = 0;
        value->it_interval.tv_sec = 0;
        value->it_interval.tv_usec = 0;
        return 0;
    }
    
    // Get timer values
    if (exo_get_timer_info(timer_cap, &remaining_ns, &interval_ns) < 0) {
        errno = EINVAL;
        return -1;
    }
    
    // Convert to timeval
    value->it_value.tv_sec = remaining_ns / NSEC_PER_SEC;
    value->it_value.tv_usec = (remaining_ns % NSEC_PER_SEC) / NSEC_PER_USEC;
    value->it_interval.tv_sec = interval_ns / NSEC_PER_SEC;
    value->it_interval.tv_usec = (interval_ns % NSEC_PER_SEC) / NSEC_PER_USEC;
    
    return 0;
}

/**
 * setitimer - Set interval timer
 * 
 * @which: Timer type
 * @value: New timer value
 * @ovalue: Buffer for old timer value (or NULL)
 * 
 * Returns 0 on success, -1 on error
 */
int
libos_setitimer(int which, const struct itimerval *value,
                struct itimerval *ovalue)
{
    uint64_t value_ns, interval_ns;
    int timer_type;
    
    if (value == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    if (init_timer() < 0)
        return -1;
    
    // Get old value if requested
    if (ovalue != NULL) {
        if (libos_getitimer(which, ovalue) < 0)
            return -1;
    }
    
    // Convert timer type
    switch (which) {
    case ITIMER_REAL:
        timer_type = EXO_ITIMER_REAL;
        break;
    case ITIMER_VIRTUAL:
        timer_type = EXO_ITIMER_VIRTUAL;
        break;
    case ITIMER_PROF:
        timer_type = EXO_ITIMER_PROF;
        break;
    default:
        errno = EINVAL;
        return -1;
    }
    
    // Convert timeval to nanoseconds
    value_ns = (uint64_t)value->it_value.tv_sec * NSEC_PER_SEC +
               value->it_value.tv_usec * NSEC_PER_USEC;
    interval_ns = (uint64_t)value->it_interval.tv_sec * NSEC_PER_SEC +
                  value->it_interval.tv_usec * NSEC_PER_USEC;
    
    // Set timer
    if (exo_set_itimer(timer_state.timer_cap, timer_type,
                       value_ns, interval_ns) < 0) {
        errno = EINVAL;
        return -1;
    }
    
    return 0;
}