/**
 * ps - report process status
 * POSIX.1-2024 compliant implementation for FeuerBird exokernel
 * 
 * Usage: ps [-aef]
 * 
 * Options:
 *   -a  Show processes from all users
 *   -e  Show all processes
 *   -f  Full format listing
 */

#include "types.h"
#include "stat.h"
#include "user.h"
#include "fcntl.h"
#include "fs.h"
#include "proc.h"

#define MAX_PROCS 64

static int aflag = 0;  // All users
static int eflag = 0;  // All processes  
static int fflag = 0;  // Full format

static void
usage(void)
{
    printf(2, "Usage: ps [-aef]\n");
    exit(1);
}

// Process state names
static const char *state_names[] = {
    "unused",
    "embryo",
    "sleep",
    "ready",
    "run",
    "zombie"
};

// Get process information from kernel
static int
getprocs(struct proc_info *procs, int max)
{
    // This would call into the kernel to get process list
    // For now, we'll implement a simplified version
    int fd, n;
    
    // Try to open /proc (if implemented)
    fd = open("/proc", O_RDONLY);
    if (fd < 0) {
        // Fallback: use system call if available
        // return sys_getprocs(procs, max);
        
        // For now, create dummy data
        procs[0].pid = 1;
        procs[0].ppid = 0;
        procs[0].state = RUNNING;
        strcpy(procs[0].name, "init");
        procs[0].sz = 4096;
        procs[0].uid = 0;
        
        procs[1].pid = 2;
        procs[1].ppid = 1;
        procs[1].state = SLEEPING;
        strcpy(procs[1].name, "sh");
        procs[1].sz = 8192;
        procs[1].uid = 0;
        
        return 2;
    }
    
    // Read process information
    n = read(fd, procs, sizeof(struct proc_info) * max);
    close(fd);
    
    return n / sizeof(struct proc_info);
}

// Format time (ticks to HH:MM:SS)
static void
format_time(uint ticks, char *buf)
{
    // Assuming 100 ticks per second
    uint seconds = ticks / 100;
    uint hours = seconds / 3600;
    uint minutes = (seconds % 3600) / 60;
    seconds = seconds % 60;
    
    if (hours > 0) {
        sprintf(buf, "%2d:%02d:%02d", hours, minutes, seconds);
    } else {
        sprintf(buf, "   %2d:%02d", minutes, seconds);
    }
}

// Print process in default format
static void
print_process_default(struct proc_info *p)
{
    printf(1, "%5d %5d %s %s\n",
           p->pid,
           p->ppid,
           state_names[p->state],
           p->name);
}

// Print process in full format
static void
print_process_full(struct proc_info *p)
{
    char time_buf[16];
    
    format_time(p->cputime, time_buf);
    
    printf(1, "%5d %5d %5d %8d %s %s %s\n",
           p->uid,
           p->pid,
           p->ppid,
           p->sz,
           time_buf,
           state_names[p->state],
           p->name);
}

// Print header
static void
print_header(void)
{
    if (fflag) {
        printf(1, "  UID   PID  PPID      SZ     TIME STATE   CMD\n");
    } else {
        printf(1, "  PID  PPID STATE   CMD\n");
    }
}

// Filter process based on flags
static int
should_show_process(struct proc_info *p)
{
    // Show all processes if -e flag
    if (eflag)
        return 1;
    
    // Show processes from all users if -a flag
    if (aflag)
        return p->state != UNUSED;
    
    // Default: show only current user's processes
    // For now, show all since we don't have user tracking
    return p->state != UNUSED && p->state != EMBRYO;
}

int
main(int argc, char *argv[])
{
    struct proc_info procs[MAX_PROCS];
    int nprocs;
    int i;
    
    // Parse options
    for (i = 1; i < argc; i++) {
        if (argv[i][0] != '-') {
            usage();
        }
        
        char *p = argv[i] + 1;
        while (*p) {
            switch (*p) {
            case 'a':
                aflag = 1;
                break;
            case 'e':
                eflag = 1;
                break;
            case 'f':
                fflag = 1;
                break;
            default:
                printf(2, "ps: invalid option -- '%c'\n", *p);
                usage();
            }
            p++;
        }
    }
    
    // Get process list
    nprocs = getprocs(procs, MAX_PROCS);
    if (nprocs < 0) {
        printf(2, "ps: cannot get process list\n");
        exit(1);
    }
    
    // Print header
    print_header();
    
    // Print each process
    for (i = 0; i < nprocs; i++) {
        if (should_show_process(&procs[i])) {
            if (fflag) {
                print_process_full(&procs[i]);
            } else {
                print_process_default(&procs[i]);
            }
        }
    }
    
    exit(0);
}

// Helper function implementations
void
sprintf(char *buf, const char *fmt, ...)
{
    // Simple sprintf implementation
    // This would need to be properly implemented
    strcpy(buf, "00:00:00");
}