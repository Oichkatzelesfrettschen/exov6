/**
 * @file ptrace.c
 * @brief Personality-aware system call tracer
 * 
 * A strace/truss/dtrace-like tool that understands all personalities
 * and can trace system calls across FeuerBird, Linux, BSD, and Illumos ABIs.
 * 
 * Usage: ptrace [-p personality] [-f] [-o output] [-e filter] command [args...]
 *        ptrace -p <pid> [-o output] [-e filter]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/time.h>
#include <getopt.h>

// Include kernel headers
#include "../kernel/sys/syscall_gateway.h"
#include "../kernel/sys/personality_debug.h"

// =============================================================================
// CONFIGURATION
// =============================================================================

#define MAX_ARGS 6
#define MAX_STRING_LEN 256
#define MAX_FILTERS 100

// Output formats
typedef enum {
    FORMAT_DEFAULT,     // Human-readable
    FORMAT_JSON,        // JSON output
    FORMAT_CSV,         // CSV format
    FORMAT_STRACE,      // strace-compatible
    FORMAT_DTRACE,      // DTrace-like
} output_format_t;

// Filter types
typedef enum {
    FILTER_SYSCALL,     // Filter by syscall name/number
    FILTER_SIGNAL,      // Filter by signal
    FILTER_FAULT,       // Filter by fault type
    FILTER_FILE,        // Filter by file operations
    FILTER_NETWORK,     // Filter by network operations
    FILTER_PROCESS,     // Filter by process operations
    FILTER_MEMORY,      // Filter by memory operations
} filter_type_t;

// Configuration
struct config {
    pid_t target_pid;                   // PID to attach to
    syscall_personality_t personality;  // Force personality
    output_format_t format;             // Output format
    FILE *output;                       // Output file
    int follow_forks;                   // Follow child processes
    int show_timestamp;                 // Show timestamps
    int show_duration;                  // Show syscall duration
    int show_stack;                     // Show stack trace
    int summary_only;                   // Only show summary
    int verbose;                        // Verbose output
    
    // Filtering
    struct {
        filter_type_t type;
        char pattern[64];
        int negate;                     // Negate filter
    } filters[MAX_FILTERS];
    int filter_count;
    
    // Statistics
    struct {
        uint64_t total_syscalls;
        uint64_t total_signals;
        uint64_t total_faults;
        uint64_t total_time;
        uint64_t syscall_counts[512];
        uint64_t syscall_times[512];
        uint64_t syscall_errors[512];
    } stats;
} config = {
    .target_pid = -1,
    .personality = PERSONALITY_FEUERBIRD,
    .format = FORMAT_DEFAULT,
    .output = NULL,
    .follow_forks = 0,
    .show_timestamp = 1,
    .show_duration = 0,
    .show_stack = 0,
    .summary_only = 0,
    .verbose = 0,
    .filter_count = 0
};

// =============================================================================
// SYSCALL DECODING
// =============================================================================

/**
 * Decode system call arguments based on type
 */
void decode_syscall_arg(char *buf, size_t len, 
                       syscall_personality_t personality,
                       int syscall_nr, int arg_num, uint64_t value) {
    // Special handling for specific syscalls and arguments
    const char *syscall_name = get_syscall_name(personality, syscall_nr);
    
    if (strcmp(syscall_name, "open") == 0 && arg_num == 0) {
        // First argument is filename - read string from process
        char filename[MAX_STRING_LEN];
        if (read_process_string(config.target_pid, value, filename, sizeof(filename)) == 0) {
            snprintf(buf, len, "\"%s\"", filename);
        } else {
            snprintf(buf, len, "%p", (void *)value);
        }
    } else if (strcmp(syscall_name, "open") == 0 && arg_num == 1) {
        // Second argument is flags
        decode_open_flags(buf, len, value);
    } else if (strcmp(syscall_name, "open") == 0 && arg_num == 2) {
        // Third argument is mode
        snprintf(buf, len, "0%lo", value);
    } else if ((strcmp(syscall_name, "read") == 0 || 
                strcmp(syscall_name, "write") == 0) && arg_num == 0) {
        // File descriptor
        snprintf(buf, len, "%d", (int)value);
    } else if ((strcmp(syscall_name, "read") == 0 || 
                strcmp(syscall_name, "write") == 0) && arg_num == 2) {
        // Size
        snprintf(buf, len, "%lu", value);
    } else if (strcmp(syscall_name, "mmap") == 0) {
        switch (arg_num) {
            case 0: // Address
                if (value == 0)
                    snprintf(buf, len, "NULL");
                else
                    snprintf(buf, len, "%p", (void *)value);
                break;
            case 1: // Length
                snprintf(buf, len, "%lu", value);
                break;
            case 2: // Protection flags
                decode_mmap_prot(buf, len, value);
                break;
            case 3: // Map flags
                decode_mmap_flags(buf, len, value);
                break;
            case 4: // File descriptor
                snprintf(buf, len, "%d", (int)value);
                break;
            case 5: // Offset
                snprintf(buf, len, "%lu", value);
                break;
        }
    } else if (personality == PERSONALITY_LINUX && 
               strcmp(syscall_name, "futex") == 0 && arg_num == 1) {
        // Linux futex operation
        decode_futex_op(buf, len, value);
    } else if (personality == PERSONALITY_ILLUMOS &&
               strcmp(syscall_name, "zone") == 0 && arg_num == 0) {
        // Illumos zone command
        decode_zone_cmd(buf, len, value);
    } else {
        // Default: hex value
        snprintf(buf, len, "0x%lx", value);
    }
}

/**
 * Decode open() flags
 */
void decode_open_flags(char *buf, size_t len, uint64_t flags) {
    buf[0] = '\0';
    
    // Access mode
    switch (flags & 0x3) {
        case 0: strcat(buf, "O_RDONLY"); break;
        case 1: strcat(buf, "O_WRONLY"); break;
        case 2: strcat(buf, "O_RDWR"); break;
    }
    
    // Additional flags
    if (flags & 0x40) strcat(buf, "|O_CREAT");
    if (flags & 0x80) strcat(buf, "|O_EXCL");
    if (flags & 0x100) strcat(buf, "|O_NOCTTY");
    if (flags & 0x200) strcat(buf, "|O_TRUNC");
    if (flags & 0x400) strcat(buf, "|O_APPEND");
    if (flags & 0x800) strcat(buf, "|O_NONBLOCK");
    if (flags & 0x80000) strcat(buf, "|O_CLOEXEC");
    
    if (strlen(buf) == 0)
        snprintf(buf, len, "0x%lx", flags);
}

/**
 * Format system call for output
 */
void format_syscall(FILE *out, debug_event_t *event) {
    char time_str[64] = "";
    char args_str[512];
    char result_str[128];
    
    // Format timestamp if requested
    if (config.show_timestamp) {
        if (config.format == FORMAT_DEFAULT) {
            snprintf(time_str, sizeof(time_str), "[%12llu] ", event->timestamp);
        } else {
            struct timeval tv;
            gettimeofday(&tv, NULL);
            snprintf(time_str, sizeof(time_str), "%ld.%06ld ", 
                    tv.tv_sec, tv.tv_usec);
        }
    }
    
    // Get syscall name
    const char *name = get_syscall_name(event->personality, 
                                       event->data.syscall.syscall_nr);
    
    // Format arguments
    args_str[0] = '\0';
    for (int i = 0; i < MAX_ARGS; i++) {
        char arg_buf[128];
        decode_syscall_arg(arg_buf, sizeof(arg_buf),
                          event->personality,
                          event->data.syscall.syscall_nr,
                          i, event->data.syscall.args[i]);
        
        if (i > 0) strcat(args_str, ", ");
        strcat(args_str, arg_buf);
    }
    
    // Format result
    if (event->type == DEBUG_EVENT_SYSCALL_EXIT) {
        if (event->data.syscall.result < 0) {
            snprintf(result_str, sizeof(result_str), " = -1 %s (%s)",
                    strerror(event->data.syscall.errno_val),
                    strerror_name(event->data.syscall.errno_val));
        } else {
            snprintf(result_str, sizeof(result_str), " = %ld",
                    event->data.syscall.result);
        }
        
        if (config.show_duration && event->data.syscall.duration > 0) {
            char duration_str[32];
            snprintf(duration_str, sizeof(duration_str), " <%llu>",
                    event->data.syscall.duration);
            strcat(result_str, duration_str);
        }
    } else {
        result_str[0] = '\0';
    }
    
    // Output based on format
    switch (config.format) {
        case FORMAT_DEFAULT:
        case FORMAT_STRACE:
            fprintf(out, "%s%s(%s)%s\n", time_str, name, args_str, result_str);
            break;
            
        case FORMAT_JSON:
            fprintf(out, "{\"time\":%llu,\"pid\":%d,\"syscall\":\"%s\","
                        "\"args\":[%s],\"result\":%ld,\"errno\":%d}\n",
                    event->timestamp, event->pid, name,
                    args_str, event->data.syscall.result,
                    event->data.syscall.errno_val);
            break;
            
        case FORMAT_CSV:
            fprintf(out, "%llu,%d,%s,%s,%ld,%d\n",
                    event->timestamp, event->pid, name,
                    args_str, event->data.syscall.result,
                    event->data.syscall.errno_val);
            break;
            
        case FORMAT_DTRACE:
            fprintf(out, "%d %llu %s:entry %s\n",
                    event->pid, event->timestamp, name, args_str);
            break;
    }
    
    // Update statistics
    if (event->type == DEBUG_EVENT_SYSCALL_EXIT) {
        int nr = event->data.syscall.syscall_nr;
        if (nr < 512) {
            config.stats.syscall_counts[nr]++;
            config.stats.syscall_times[nr] += event->data.syscall.duration;
            if (event->data.syscall.result < 0)
                config.stats.syscall_errors[nr]++;
        }
        config.stats.total_syscalls++;
        config.stats.total_time += event->data.syscall.duration;
    }
}

// =============================================================================
// PROCESS CONTROL
// =============================================================================

/**
 * Attach to process for tracing
 */
int attach_process(pid_t pid) {
    // Enable debugging for process
    uint32_t trace_mode = TRACE_MODE_SYSCALL;
    
    if (config.verbose) {
        trace_mode |= TRACE_MODE_SIGNAL | TRACE_MODE_FAULT | 
                      TRACE_MODE_PERSONALITY;
    }
    
    if (sys_debug_attach(pid, trace_mode) < 0) {
        fprintf(stderr, "Failed to attach to PID %d: %s\n", 
                pid, strerror(errno));
        return -1;
    }
    
    config.target_pid = pid;
    
    if (config.verbose) {
        fprintf(stderr, "Attached to PID %d\n", pid);
    }
    
    return 0;
}

/**
 * Detach from process
 */
int detach_process(pid_t pid) {
    if (sys_debug_detach(pid) < 0) {
        fprintf(stderr, "Failed to detach from PID %d: %s\n",
                pid, strerror(errno));
        return -1;
    }
    
    if (config.verbose) {
        fprintf(stderr, "Detached from PID %d\n", pid);
    }
    
    return 0;
}

/**
 * Main trace loop
 */
int trace_loop(void) {
    debug_event_t events[100];
    uint32_t count;
    int running = 1;
    
    while (running) {
        // Get debug events
        count = 100;
        if (sys_debug_get_events(events, &count) < 0) {
            fprintf(stderr, "Failed to get debug events: %s\n", 
                    strerror(errno));
            break;
        }
        
        // Process events
        for (uint32_t i = 0; i < count; i++) {
            debug_event_t *event = &events[i];
            
            // Apply filters
            if (!should_trace_event(event))
                continue;
            
            // Format and output event
            switch (event->type) {
                case DEBUG_EVENT_SYSCALL_ENTER:
                case DEBUG_EVENT_SYSCALL_EXIT:
                    if (!config.summary_only) {
                        format_syscall(config.output ?: stdout, event);
                    }
                    break;
                    
                case DEBUG_EVENT_SIGNAL_SEND:
                case DEBUG_EVENT_SIGNAL_DELIVER:
                    if (config.verbose && !config.summary_only) {
                        format_signal(config.output ?: stdout, event);
                    }
                    break;
                    
                case DEBUG_EVENT_PERSONALITY_CHANGE:
                    if (config.verbose) {
                        fprintf(config.output ?: stdout,
                                "--- Personality changed: %s -> %s ---\n",
                                get_personality_name(event->data.personality.old_personality),
                                get_personality_name(event->data.personality.new_personality));
                    }
                    break;
                    
                case DEBUG_EVENT_EXIT:
                    fprintf(config.output ?: stdout,
                            "+++ exited with %ld +++\n",
                            event->data.syscall.result);
                    running = 0;
                    break;
                    
                case DEBUG_EVENT_FORK:
                    if (config.follow_forks) {
                        attach_process(event->data.syscall.result);
                        fprintf(config.output ?: stdout,
                                "--- Process %ld attached ---\n",
                                event->data.syscall.result);
                    }
                    break;
            }
        }
        
        // Small delay to avoid busy-waiting
        if (count == 0) {
            usleep(1000);  // 1ms
        }
    }
    
    return 0;
}

// =============================================================================
// FILTERING
// =============================================================================

/**
 * Check if event should be traced based on filters
 */
int should_trace_event(debug_event_t *event) {
    if (config.filter_count == 0)
        return 1;  // No filters, trace everything
    
    for (int i = 0; i < config.filter_count; i++) {
        int matches = 0;
        
        switch (config.filters[i].type) {
            case FILTER_SYSCALL:
                if (event->type == DEBUG_EVENT_SYSCALL_ENTER ||
                    event->type == DEBUG_EVENT_SYSCALL_EXIT) {
                    const char *name = get_syscall_name(event->personality,
                                                       event->data.syscall.syscall_nr);
                    if (strstr(name, config.filters[i].pattern))
                        matches = 1;
                }
                break;
                
            case FILTER_FILE:
                // Filter file-related syscalls
                if (event->type == DEBUG_EVENT_SYSCALL_ENTER ||
                    event->type == DEBUG_EVENT_SYSCALL_EXIT) {
                    const char *name = get_syscall_name(event->personality,
                                                       event->data.syscall.syscall_nr);
                    if (strstr(name, "open") || strstr(name, "read") ||
                        strstr(name, "write") || strstr(name, "close") ||
                        strstr(name, "stat") || strstr(name, "lseek"))
                        matches = 1;
                }
                break;
                
            case FILTER_NETWORK:
                // Filter network-related syscalls
                if (event->type == DEBUG_EVENT_SYSCALL_ENTER ||
                    event->type == DEBUG_EVENT_SYSCALL_EXIT) {
                    const char *name = get_syscall_name(event->personality,
                                                       event->data.syscall.syscall_nr);
                    if (strstr(name, "socket") || strstr(name, "connect") ||
                        strstr(name, "bind") || strstr(name, "listen") ||
                        strstr(name, "accept") || strstr(name, "send") ||
                        strstr(name, "recv"))
                        matches = 1;
                }
                break;
        }
        
        if (config.filters[i].negate)
            matches = !matches;
        
        if (matches)
            return 1;
    }
    
    return 0;
}

// =============================================================================
// SUMMARY OUTPUT
// =============================================================================

/**
 * Print summary statistics
 */
void print_summary(void) {
    if (config.stats.total_syscalls == 0) {
        fprintf(stderr, "No syscalls traced\n");
        return;
    }
    
    FILE *out = config.output ?: stdout;
    
    fprintf(out, "\n%% time     seconds  usecs/call     calls    errors syscall\n");
    fprintf(out, "------ ----------- ----------- --------- --------- ----------------\n");
    
    // Sort syscalls by time
    struct {
        int syscall_nr;
        uint64_t time;
        uint64_t count;
        uint64_t errors;
    } sorted[512];
    int sorted_count = 0;
    
    for (int i = 0; i < 512; i++) {
        if (config.stats.syscall_counts[i] > 0) {
            sorted[sorted_count].syscall_nr = i;
            sorted[sorted_count].time = config.stats.syscall_times[i];
            sorted[sorted_count].count = config.stats.syscall_counts[i];
            sorted[sorted_count].errors = config.stats.syscall_errors[i];
            sorted_count++;
        }
    }
    
    // Sort by time (bubble sort for simplicity)
    for (int i = 0; i < sorted_count - 1; i++) {
        for (int j = 0; j < sorted_count - i - 1; j++) {
            if (sorted[j].time < sorted[j + 1].time) {
                struct { int nr; uint64_t t, c, e; } tmp = sorted[j];
                sorted[j] = sorted[j + 1];
                sorted[j + 1] = tmp;
            }
        }
    }
    
    // Print sorted results
    for (int i = 0; i < sorted_count; i++) {
        double percent = (100.0 * sorted[i].time) / config.stats.total_time;
        double seconds = sorted[i].time / 1000000000.0;
        uint64_t usecs_per_call = sorted[i].time / sorted[i].count / 1000;
        
        const char *name = get_syscall_name(PERSONALITY_FEUERBIRD, 
                                           sorted[i].syscall_nr);
        
        fprintf(out, "%6.2f %11.6f %11llu %9llu %9llu %s\n",
                percent, seconds, usecs_per_call,
                sorted[i].count, sorted[i].errors, name);
    }
    
    fprintf(out, "------ ----------- ----------- --------- --------- ----------------\n");
    fprintf(out, "100.00 %11.6f             %9llu %9llu total\n",
            config.stats.total_time / 1000000000.0,
            config.stats.total_syscalls,
            config.stats.syscall_errors[0]); // Total errors
}

// =============================================================================
// MAIN PROGRAM
// =============================================================================

/**
 * Print usage information
 */
void usage(const char *prog) {
    fprintf(stderr, "Usage: %s [options] command [args...]\n", prog);
    fprintf(stderr, "       %s -p <pid> [options]\n", prog);
    fprintf(stderr, "\nOptions:\n");
    fprintf(stderr, "  -p <pid>        Attach to existing process\n");
    fprintf(stderr, "  -P <personality> Force personality (linux/bsd/illumos/posix)\n");
    fprintf(stderr, "  -f              Follow forks\n");
    fprintf(stderr, "  -o <file>       Output to file\n");
    fprintf(stderr, "  -e <filter>     Filter expression\n");
    fprintf(stderr, "  -t              Show timestamps\n");
    fprintf(stderr, "  -T              Show syscall duration\n");
    fprintf(stderr, "  -c              Summary only\n");
    fprintf(stderr, "  -v              Verbose output\n");
    fprintf(stderr, "  -F <format>     Output format (default/json/csv/strace/dtrace)\n");
    fprintf(stderr, "\nFilter examples:\n");
    fprintf(stderr, "  -e trace=open,read,write   Trace specific syscalls\n");
    fprintf(stderr, "  -e trace=file              Trace file operations\n");
    fprintf(stderr, "  -e trace=network           Trace network operations\n");
    fprintf(stderr, "  -e trace=!open             Exclude specific syscalls\n");
    exit(1);
}

int main(int argc, char *argv[]) {
    int opt;
    pid_t pid = -1;
    char *command = NULL;
    char **command_args = NULL;
    
    // Parse options
    while ((opt = getopt(argc, argv, "p:P:fo:e:tTcvF:h")) != -1) {
        switch (opt) {
            case 'p':
                pid = atoi(optarg);
                break;
                
            case 'P':
                if (strcmp(optarg, "linux") == 0)
                    config.personality = PERSONALITY_LINUX;
                else if (strcmp(optarg, "bsd") == 0)
                    config.personality = PERSONALITY_BSD;
                else if (strcmp(optarg, "illumos") == 0)
                    config.personality = PERSONALITY_ILLUMOS;
                else if (strcmp(optarg, "posix") == 0)
                    config.personality = PERSONALITY_POSIX2024;
                else {
                    fprintf(stderr, "Unknown personality: %s\n", optarg);
                    exit(1);
                }
                break;
                
            case 'f':
                config.follow_forks = 1;
                break;
                
            case 'o':
                config.output = fopen(optarg, "w");
                if (!config.output) {
                    fprintf(stderr, "Cannot open output file: %s\n", optarg);
                    exit(1);
                }
                break;
                
            case 'e':
                parse_filter(optarg);
                break;
                
            case 't':
                config.show_timestamp = 1;
                break;
                
            case 'T':
                config.show_duration = 1;
                break;
                
            case 'c':
                config.summary_only = 1;
                break;
                
            case 'v':
                config.verbose = 1;
                break;
                
            case 'F':
                if (strcmp(optarg, "json") == 0)
                    config.format = FORMAT_JSON;
                else if (strcmp(optarg, "csv") == 0)
                    config.format = FORMAT_CSV;
                else if (strcmp(optarg, "strace") == 0)
                    config.format = FORMAT_STRACE;
                else if (strcmp(optarg, "dtrace") == 0)
                    config.format = FORMAT_DTRACE;
                else
                    config.format = FORMAT_DEFAULT;
                break;
                
            case 'h':
            default:
                usage(argv[0]);
        }
    }
    
    // Check if we're attaching to existing process or starting new one
    if (pid > 0) {
        // Attach to existing process
        if (attach_process(pid) < 0)
            exit(1);
    } else if (optind < argc) {
        // Start new process
        command = argv[optind];
        command_args = &argv[optind];
        
        pid = fork();
        if (pid == 0) {
            // Child: execute command
            execvp(command, command_args);
            fprintf(stderr, "Failed to execute %s: %s\n", 
                    command, strerror(errno));
            exit(1);
        } else if (pid < 0) {
            fprintf(stderr, "Failed to fork: %s\n", strerror(errno));
            exit(1);
        }
        
        // Parent: attach to child
        if (attach_process(pid) < 0)
            exit(1);
    } else {
        usage(argv[0]);
    }
    
    // Install signal handler for cleanup
    signal(SIGINT, cleanup_handler);
    signal(SIGTERM, cleanup_handler);
    
    // Main trace loop
    trace_loop();
    
    // Print summary if requested
    if (config.summary_only || config.verbose) {
        print_summary();
    }
    
    // Cleanup
    detach_process(pid);
    
    if (config.output)
        fclose(config.output);
    
    return 0;
}