#pragma once

/**
 * @file time.h
 * @brief Time functions and types - POSIX-2024 compliant
 */

#include <sys/types.h>
#include <stdint.h>

// Forward declarations
struct sigevent;
struct itimerspec;

// Clock types
#define CLOCK_REALTIME           0
#define CLOCK_MONOTONIC          1
#define CLOCK_PROCESS_CPUTIME_ID 2
#define CLOCK_THREAD_CPUTIME_ID  3

// Timer constants
#define TIMER_ABSTIME 1

// Time structure
struct tm {
    int tm_sec;    // Seconds [0,60]
    int tm_min;    // Minutes [0,59]  
    int tm_hour;   // Hours [0,23]
    int tm_mday;   // Day of month [1,31]
    int tm_mon;    // Month of year [0,11]
    int tm_year;   // Years since 1900
    int tm_wday;   // Day of week [0,6] (Sunday = 0)
    int tm_yday;   // Day of year [0,365]
    int tm_isdst;  // Daylight saving time flag
};

// Interval timer value
struct itimerspec {
    struct timespec it_interval;  // Timer interval
    struct timespec it_value;     // Timer expiration
};

// Clock functions
int clock_gettime(clockid_t clock_id, struct timespec* tp);
int clock_settime(clockid_t clock_id, const struct timespec* tp);
int clock_getres(clockid_t clock_id, struct timespec* res);
int clock_nanosleep(clockid_t clock_id, int flags,
                   const struct timespec* request, struct timespec* remain);

// Timer functions
int timer_create(clockid_t clock_id, struct sigevent* sevp, timer_t* timerid);
int timer_delete(timer_t timerid);
int timer_settime(timer_t timerid, int flags,
                 const struct itimerspec* new_value, struct itimerspec* old_value);
int timer_gettime(timer_t timerid, struct itimerspec* curr_value);
int timer_getoverrun(timer_t timerid);

// Time conversion
time_t time(time_t* tloc);
char* ctime(const time_t* timep);
char* ctime_r(const time_t* timep, char* buf);
struct tm* gmtime(const time_t* timep);
struct tm* gmtime_r(const time_t* timep, struct tm* result);
struct tm* localtime(const time_t* timep);
struct tm* localtime_r(const time_t* timep, struct tm* result);
time_t mktime(struct tm* tm);
double difftime(time_t time1, time_t time0);

// String formatting
size_t strftime(char* restrict s, size_t maxsize,
               const char* restrict format, const struct tm* restrict tm);
char* strptime(const char* restrict s, const char* restrict format,
              struct tm* restrict tm);

// ASCII time
char* asctime(const struct tm* tm);
char* asctime_r(const struct tm* tm, char* buf);

// Sleep functions
int nanosleep(const struct timespec* req, struct timespec* rem);

// Global timezone variables
extern long timezone;
extern int daylight;
extern char* tzname[2];

// Timezone functions
void tzset(void);

// Clock function
clock_t clock(void);

#define CLOCKS_PER_SEC 1000000L

// Static assertions
_Static_assert(sizeof(struct timespec) >= 16, "timespec too small");
_Static_assert(sizeof(time_t) >= 8, "time_t should be 64-bit");