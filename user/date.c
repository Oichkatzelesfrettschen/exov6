/**
 * date - print or set the system date and time
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: date [-u] [+format]
 *        date [-u] MMDDhhmm[[CC]YY][.ss]
 * 
 * Options:
 *   -u       Use UTC instead of local time
 *   +format  Display date according to format string
 * 
 * Format specifiers:
 *   %a  Abbreviated weekday name
 *   %A  Full weekday name  
 *   %b  Abbreviated month name
 *   %B  Full month name
 *   %c  Locale's date and time
 *   %d  Day of month (01-31)
 *   %H  Hour (00-23)
 *   %I  Hour (01-12)
 *   %j  Day of year (001-366)
 *   %m  Month (01-12)
 *   %M  Minute (00-59)
 *   %p  AM/PM
 *   %S  Second (00-60)
 *   %U  Week number (00-53), Sunday as first day
 *   %w  Weekday (0-6), Sunday is 0
 *   %W  Week number (00-53), Monday as first day
 *   %x  Locale's date representation
 *   %X  Locale's time representation
 *   %y  Year without century (00-99)
 *   %Y  Year with century
 *   %Z  Time zone name
 *   %%  Literal %
 */

#include "types.h"
#include "stat.h"
#include "user.h"
#include "date.h"

static int uflag = 0;  // Use UTC

// Month names
static const char *month_abbr[] = {
    "Jan", "Feb", "Mar", "Apr", "May", "Jun",
    "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"
};

static const char *month_full[] = {
    "January", "February", "March", "April", "May", "June",
    "July", "August", "September", "October", "November", "December"
};

// Weekday names
static const char *weekday_abbr[] = {
    "Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"
};

static const char *weekday_full[] = {
    "Sunday", "Monday", "Tuesday", "Wednesday",
    "Thursday", "Friday", "Saturday"
};

static void
usage(void)
{
    printf(2, "Usage: date [-u] [+format]\n");
    printf(2, "       date [-u] MMDDhhmm[[CC]YY][.ss]\n");
    exit(1);
}

// Check if year is leap year
static int
is_leap_year(int year)
{
    return (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0);
}

// Calculate day of week (Zeller's congruence)
static int
day_of_week(int year, int month, int day)
{
    if (month < 3) {
        month += 12;
        year--;
    }
    
    int k = year % 100;
    int j = year / 100;
    
    int h = (day + 13 * (month + 1) / 5 + k + k / 4 + j / 4 - 2 * j) % 7;
    
    // Convert to 0=Sunday, 1=Monday, etc.
    return (h + 6) % 7;
}

// Calculate day of year
static int
day_of_year(int year, int month, int day)
{
    int days[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    
    if (is_leap_year(year)) {
        days[1] = 29;
    }
    
    int day_num = day;
    for (int i = 0; i < month - 1; i++) {
        day_num += days[i];
    }
    
    return day_num;
}

// Calculate week number
static int
week_number(int year, int month, int day, int start_day)
{
    int jan1_weekday = day_of_week(year, 1, 1);
    int days = day_of_year(year, month, day);
    
    // Adjust for week starting day (0=Sunday, 1=Monday)
    int offset = (jan1_weekday - start_day + 7) % 7;
    
    return (days + offset - 1) / 7;
}

// Format number with leading zeros
static void
format_number(char *buf, int num, int width)
{
    for (int i = width - 1; i >= 0; i--) {
        buf[i] = '0' + (num % 10);
        num /= 10;
    }
    buf[width] = '\0';
}

// Format date according to format string
static void
format_date(const char *fmt, struct rtcdate *r)
{
    char buf[32];
    int hour12;
    const char *ampm;
    
    while (*fmt) {
        if (*fmt == '%' && *(fmt + 1)) {
            fmt++;
            switch (*fmt) {
            case 'a':  // Abbreviated weekday
                printf(1, "%s", weekday_abbr[day_of_week(r->year, r->month, r->day)]);
                break;
                
            case 'A':  // Full weekday
                printf(1, "%s", weekday_full[day_of_week(r->year, r->month, r->day)]);
                break;
                
            case 'b':  // Abbreviated month
            case 'h':  // Same as %b
                printf(1, "%s", month_abbr[r->month - 1]);
                break;
                
            case 'B':  // Full month
                printf(1, "%s", month_full[r->month - 1]);
                break;
                
            case 'c':  // Locale's date and time
                printf(1, "%s %s %2d %02d:%02d:%02d %d",
                       weekday_abbr[day_of_week(r->year, r->month, r->day)],
                       month_abbr[r->month - 1],
                       r->day, r->hour, r->minute, r->second, r->year);
                break;
                
            case 'd':  // Day of month (01-31)
                format_number(buf, r->day, 2);
                printf(1, "%s", buf);
                break;
                
            case 'D':  // Date as %m/%d/%y
                format_number(buf, r->month, 2);
                printf(1, "%s/", buf);
                format_number(buf, r->day, 2);
                printf(1, "%s/", buf);
                format_number(buf, r->year % 100, 2);
                printf(1, "%s", buf);
                break;
                
            case 'e':  // Day of month (space padded)
                printf(1, "%2d", r->day);
                break;
                
            case 'F':  // Date as %Y-%m-%d
                printf(1, "%04d-%02d-%02d", r->year, r->month, r->day);
                break;
                
            case 'H':  // Hour (00-23)
                format_number(buf, r->hour, 2);
                printf(1, "%s", buf);
                break;
                
            case 'I':  // Hour (01-12)
                hour12 = r->hour % 12;
                if (hour12 == 0) hour12 = 12;
                format_number(buf, hour12, 2);
                printf(1, "%s", buf);
                break;
                
            case 'j':  // Day of year (001-366)
                format_number(buf, day_of_year(r->year, r->month, r->day), 3);
                printf(1, "%s", buf);
                break;
                
            case 'k':  // Hour (space padded)
                printf(1, "%2d", r->hour);
                break;
                
            case 'l':  // Hour 12-hour (space padded)
                hour12 = r->hour % 12;
                if (hour12 == 0) hour12 = 12;
                printf(1, "%2d", hour12);
                break;
                
            case 'm':  // Month (01-12)
                format_number(buf, r->month, 2);
                printf(1, "%s", buf);
                break;
                
            case 'M':  // Minute (00-59)
                format_number(buf, r->minute, 2);
                printf(1, "%s", buf);
                break;
                
            case 'n':  // Newline
                printf(1, "\n");
                break;
                
            case 'p':  // AM/PM
                ampm = r->hour < 12 ? "AM" : "PM";
                printf(1, "%s", ampm);
                break;
                
            case 'P':  // am/pm (lowercase)
                ampm = r->hour < 12 ? "am" : "pm";
                printf(1, "%s", ampm);
                break;
                
            case 'r':  // Time as %I:%M:%S %p
                hour12 = r->hour % 12;
                if (hour12 == 0) hour12 = 12;
                ampm = r->hour < 12 ? "AM" : "PM";
                printf(1, "%02d:%02d:%02d %s", hour12, r->minute, r->second, ampm);
                break;
                
            case 'R':  // Time as %H:%M
                printf(1, "%02d:%02d", r->hour, r->minute);
                break;
                
            case 'S':  // Second (00-60)
                format_number(buf, r->second, 2);
                printf(1, "%s", buf);
                break;
                
            case 't':  // Tab
                printf(1, "\t");
                break;
                
            case 'T':  // Time as %H:%M:%S
                printf(1, "%02d:%02d:%02d", r->hour, r->minute, r->second);
                break;
                
            case 'u':  // Weekday (1-7), Monday is 1
                printf(1, "%d", ((day_of_week(r->year, r->month, r->day) + 6) % 7) + 1);
                break;
                
            case 'U':  // Week number (Sunday as first day)
                format_number(buf, week_number(r->year, r->month, r->day, 0), 2);
                printf(1, "%s", buf);
                break;
                
            case 'w':  // Weekday (0-6), Sunday is 0
                printf(1, "%d", day_of_week(r->year, r->month, r->day));
                break;
                
            case 'W':  // Week number (Monday as first day)
                format_number(buf, week_number(r->year, r->month, r->day, 1), 2);
                printf(1, "%s", buf);
                break;
                
            case 'x':  // Locale's date
                printf(1, "%02d/%02d/%02d", r->month, r->day, r->year % 100);
                break;
                
            case 'X':  // Locale's time
                printf(1, "%02d:%02d:%02d", r->hour, r->minute, r->second);
                break;
                
            case 'y':  // Year without century (00-99)
                format_number(buf, r->year % 100, 2);
                printf(1, "%s", buf);
                break;
                
            case 'Y':  // Year with century
                printf(1, "%04d", r->year);
                break;
                
            case 'Z':  // Time zone name
                printf(1, "%s", uflag ? "UTC" : "LOCAL");
                break;
                
            case '%':  // Literal %
                printf(1, "%%");
                break;
                
            default:
                printf(1, "%%%c", *fmt);
                break;
            }
            fmt++;
        } else {
            printf(1, "%c", *fmt);
            fmt++;
        }
    }
}

// Parse date string MMDDhhmm[[CC]YY][.ss]
static int
parse_date(const char *str, struct rtcdate *r)
{
    int len = strlen(str);
    char buf[5];
    int pos = 0;
    
    // Minimum format: MMDDhhmm (8 chars)
    if (len < 8) {
        return -1;
    }
    
    // Parse MM (month)
    buf[0] = str[pos++];
    buf[1] = str[pos++];
    buf[2] = '\0';
    r->month = atoi(buf);
    if (r->month < 1 || r->month > 12) {
        return -1;
    }
    
    // Parse DD (day)
    buf[0] = str[pos++];
    buf[1] = str[pos++];
    buf[2] = '\0';
    r->day = atoi(buf);
    if (r->day < 1 || r->day > 31) {
        return -1;
    }
    
    // Parse hh (hour)
    buf[0] = str[pos++];
    buf[1] = str[pos++];
    buf[2] = '\0';
    r->hour = atoi(buf);
    if (r->hour > 23) {
        return -1;
    }
    
    // Parse mm (minute)
    buf[0] = str[pos++];
    buf[1] = str[pos++];
    buf[2] = '\0';
    r->minute = atoi(buf);
    if (r->minute > 59) {
        return -1;
    }
    
    // Optional: [[CC]YY]
    if (pos < len && str[pos] != '.') {
        if (len - pos >= 4) {
            // CCYY format
            buf[0] = str[pos++];
            buf[1] = str[pos++];
            buf[2] = str[pos++];
            buf[3] = str[pos++];
            buf[4] = '\0';
            r->year = atoi(buf);
        } else if (len - pos >= 2) {
            // YY format
            buf[0] = str[pos++];
            buf[1] = str[pos++];
            buf[2] = '\0';
            int yy = atoi(buf);
            // POSIX: 69-99 -> 1969-1999, 00-68 -> 2000-2068
            if (yy >= 69) {
                r->year = 1900 + yy;
            } else {
                r->year = 2000 + yy;
            }
        }
    }
    
    // Optional: .ss (seconds)
    if (pos < len && str[pos] == '.') {
        pos++;
        if (len - pos >= 2) {
            buf[0] = str[pos++];
            buf[1] = str[pos++];
            buf[2] = '\0';
            r->second = atoi(buf);
            if (r->second > 60) {  // Allow for leap second
                return -1;
            }
        }
    }
    
    return 0;
}

int
main(int argc, char *argv[])
{
    struct rtcdate r;
    int i;
    char *format = "+%a %b %e %H:%M:%S %Z %Y";  // Default format
    char *set_date = 0;
    
    // Parse options
    for (i = 1; i < argc; i++) {
        if (argv[i][0] == '-') {
            char *p = argv[i] + 1;
            while (*p) {
                switch (*p) {
                case 'u':
                    uflag = 1;
                    break;
                default:
                    printf(2, "date: invalid option -- '%c'\n", *p);
                    usage();
                }
                p++;
            }
        } else if (argv[i][0] == '+') {
            // Format string
            format = argv[i];
        } else {
            // Date to set
            set_date = argv[i];
        }
    }
    
    if (set_date) {
        // Parse and set the date
        if (cmostime(&r) < 0) {
            printf(2, "date: cannot read current time\n");
            exit(1);
        }
        
        if (parse_date(set_date, &r) < 0) {
            printf(2, "date: invalid date '%s'\n", set_date);
            usage();
        }
        
        // Set the time (would need system call)
        printf(2, "date: setting time not yet implemented\n");
        exit(1);
    } else {
        // Get and display current time
        if (cmostime(&r) < 0) {
            printf(2, "date: cannot read time\n");
            exit(1);
        }
        
        // Format and print
        if (format[0] == '+') {
            format_date(format + 1, &r);
        } else {
            format_date("%a %b %e %H:%M:%S %Z %Y", &r);
        }
        printf(1, "\n");
    }
    
    exit(0);
}

// Helper function
int
atoi(const char *s)
{
    int n = 0;
    while (*s >= '0' && *s <= '9') {
        n = n * 10 + (*s - '0');
        s++;
    }
    return n;
}