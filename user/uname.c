/**
 * uname - print system information
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: uname [-amnrsv]
 * 
 * Options:
 *   -a  Print all information
 *   -m  Print machine hardware name
 *   -n  Print network node hostname
 *   -r  Print kernel release
 *   -s  Print kernel name (default)
 *   -v  Print kernel version
 */

#include "types.h"
#include "stat.h"
#include "user.h"
#include "param.h"

// System information structure
struct utsname {
    char sysname[65];    // Operating system name
    char nodename[65];   // Network node hostname
    char release[65];    // Operating system release
    char version[65];    // Operating system version
    char machine[65];    // Hardware identifier
};

// Flags for what to print
static int print_sysname = 0;
static int print_nodename = 0;
static int print_release = 0;
static int print_version = 0;
static int print_machine = 0;
static int print_all = 0;

static void
usage(void)
{
    printf(2, "Usage: uname [-amnrsv]\n");
    exit(1);
}

// Get system information
static void
get_uname(struct utsname *u)
{
    // Fill in system information
    // These would normally come from kernel
    
    // System name
    strcpy(u->sysname, "FeuerBird");
    
    // Node name (hostname)
    strcpy(u->nodename, "exokernel");
    
    // Release version
    strcpy(u->release, "6.0-EXOKERNEL");
    
    // Version details
    strcpy(u->version, "#1 SMP POSIX-2024 C17");
    
    // Machine hardware
#ifdef __x86_64__
    strcpy(u->machine, "x86_64");
#elif defined(__i386__)
    strcpy(u->machine, "i686");
#elif defined(__aarch64__)
    strcpy(u->machine, "aarch64");
#elif defined(__arm__)
    strcpy(u->machine, "armv7l");
#elif defined(__powerpc64__)
    strcpy(u->machine, "ppc64le");
#elif defined(__powerpc__)
    strcpy(u->machine, "ppc");
#else
    strcpy(u->machine, "unknown");
#endif
}

// Print selected information
static void
print_uname(struct utsname *u)
{
    int first = 1;
    
    if (print_sysname || print_all) {
        printf(1, "%s", u->sysname);
        first = 0;
    }
    
    if (print_nodename || print_all) {
        if (!first) printf(1, " ");
        printf(1, "%s", u->nodename);
        first = 0;
    }
    
    if (print_release || print_all) {
        if (!first) printf(1, " ");
        printf(1, "%s", u->release);
        first = 0;
    }
    
    if (print_version || print_all) {
        if (!first) printf(1, " ");
        printf(1, "%s", u->version);
        first = 0;
    }
    
    if (print_machine || print_all) {
        if (!first) printf(1, " ");
        printf(1, "%s", u->machine);
        first = 0;
    }
    
    printf(1, "\n");
}

int
main(int argc, char *argv[])
{
    struct utsname u;
    int i;
    int any_flag = 0;
    
    // Parse options
    for (i = 1; i < argc; i++) {
        if (argv[i][0] != '-') {
            usage();
        }
        
        char *p = argv[i] + 1;
        while (*p) {
            switch (*p) {
            case 'a':  // All information
                print_all = 1;
                any_flag = 1;
                break;
                
            case 'm':  // Machine hardware
                print_machine = 1;
                any_flag = 1;
                break;
                
            case 'n':  // Node name
                print_nodename = 1;
                any_flag = 1;
                break;
                
            case 'r':  // Release
                print_release = 1;
                any_flag = 1;
                break;
                
            case 's':  // System name
                print_sysname = 1;
                any_flag = 1;
                break;
                
            case 'v':  // Version
                print_version = 1;
                any_flag = 1;
                break;
                
            default:
                printf(2, "uname: invalid option -- '%c'\n", *p);
                usage();
            }
            p++;
        }
    }
    
    // Default: print system name
    if (!any_flag) {
        print_sysname = 1;
    }
    
    // Get system information
    get_uname(&u);
    
    // Print requested information
    print_uname(&u);
    
    exit(0);
}