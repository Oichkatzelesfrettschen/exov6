/**
 * id - print real and effective user and group IDs
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: id [user]
 *        id -G [-n] [user]
 *        id -g [-nr] [user]
 *        id -u [-nr] [user]
 * 
 * Options:
 *   -G  Print all group IDs
 *   -g  Print only effective group ID
 *   -n  Print name instead of number
 *   -r  Print real ID instead of effective
 *   -u  Print only effective user ID
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"
#include "fcntl.h"

#define MAX_GROUPS 32
#define MAX_LINE 256

// Option flags
static int Gflag = 0;  // Print all groups
static int gflag = 0;  // Print only group ID
static int nflag = 0;  // Print names
static int rflag = 0;  // Print real IDs
static int uflag = 0;  // Print only user ID

// User/group database entry
typedef struct {
    char name[32];
    int id;
} id_entry;

// Simple user/group databases
static id_entry users[] = {
    {"root", 0},
    {"daemon", 1},
    {"bin", 2},
    {"sys", 3},
    {"adm", 4},
    {"user", 1000},
    {"guest", 9999},
    {"", -1}
};

static id_entry groups[] = {
    {"root", 0},
    {"daemon", 1},
    {"bin", 2},
    {"sys", 3},
    {"adm", 4},
    {"tty", 5},
    {"disk", 6},
    {"wheel", 10},
    {"users", 100},
    {"staff", 50},
    {"", -1}
};

static void
usage(void)
{
    printf(2, "Usage: id [user]\n");
    printf(2, "       id -G [-n] [user]\n");
    printf(2, "       id -g [-nr] [user]\n");
    printf(2, "       id -u [-nr] [user]\n");
    exit(1);
}

// Get user name from uid
static const char *
get_username(uid_t uid)
{
    for (int i = 0; users[i].id >= 0; i++) {
        if (users[i].id == uid) {
            return users[i].name;
        }
    }
    return 0;
}

// Get group name from gid
static const char *
get_groupname(gid_t gid)
{
    for (int i = 0; groups[i].id >= 0; i++) {
        if (groups[i].id == gid) {
            return groups[i].name;
        }
    }
    return 0;
}

// Get uid from username
static uid_t
get_uid(const char *name)
{
    for (int i = 0; users[i].id >= 0; i++) {
        if (strcmp(users[i].name, name) == 0) {
            return users[i].id;
        }
    }
    return -1;
}

// Print user ID
static void
print_uid(uid_t uid, int use_name)
{
    if (use_name) {
        const char *name = get_username(uid);
        if (name) {
            printf(1, "%s", name);
        } else {
            printf(1, "%d", uid);
        }
    } else {
        printf(1, "%d", uid);
    }
}

// Print group ID
static void
print_gid(gid_t gid, int use_name)
{
    if (use_name) {
        const char *name = get_groupname(gid);
        if (name) {
            printf(1, "%s", name);
        } else {
            printf(1, "%d", gid);
        }
    } else {
        printf(1, "%d", gid);
    }
}

// Print all groups
static void
print_groups(gid_t *groups, int ngroups, int use_name)
{
    for (int i = 0; i < ngroups; i++) {
        if (i > 0) printf(1, " ");
        print_gid(groups[i], use_name);
    }
}

// Get process IDs (simulated)
static void
get_process_ids(uid_t *ruid, uid_t *euid, gid_t *rgid, gid_t *egid,
                gid_t *groups, int *ngroups)
{
    // In a real system, these would come from the kernel
    // For now, simulate some values
    *ruid = 1000;  // Real user ID
    *euid = 1000;  // Effective user ID
    *rgid = 100;   // Real group ID
    *egid = 100;   // Effective group ID
    
    // Supplementary groups
    groups[0] = 100;  // Primary group
    groups[1] = 10;   // wheel
    groups[2] = 50;   // staff
    *ngroups = 3;
}

// Print full ID information
static void
print_full_id(uid_t ruid, uid_t euid, gid_t rgid, gid_t egid,
              gid_t *groups, int ngroups)
{
    const char *username, *groupname;
    
    // Print user ID
    printf(1, "uid=%d", ruid);
    username = get_username(ruid);
    if (username) {
        printf(1, "(%s)", username);
    }
    
    // Print effective user ID if different
    if (euid != ruid) {
        printf(1, " euid=%d", euid);
        username = get_username(euid);
        if (username) {
            printf(1, "(%s)", username);
        }
    }
    
    // Print group ID
    printf(1, " gid=%d", rgid);
    groupname = get_groupname(rgid);
    if (groupname) {
        printf(1, "(%s)", groupname);
    }
    
    // Print effective group ID if different
    if (egid != rgid) {
        printf(1, " egid=%d", egid);
        groupname = get_groupname(egid);
        if (groupname) {
            printf(1, "(%s)", groupname);
        }
    }
    
    // Print supplementary groups
    if (ngroups > 0) {
        printf(1, " groups=");
        for (int i = 0; i < ngroups; i++) {
            if (i > 0) printf(1, ",");
            printf(1, "%d", groups[i]);
            groupname = get_groupname(groups[i]);
            if (groupname) {
                printf(1, "(%s)", groupname);
            }
        }
    }
    
    printf(1, "\n");
}

int
main(int argc, char *argv[])
{
    uid_t ruid, euid;
    gid_t rgid, egid;
    gid_t groups[MAX_GROUPS];
    int ngroups;
    char *username = 0;
    int i;
    
    // Parse options
    for (i = 1; i < argc; i++) {
        if (argv[i][0] == '-') {
            char *p = argv[i] + 1;
            while (*p) {
                switch (*p) {
                case 'G':  // All groups
                    Gflag = 1;
                    break;
                case 'g':  // Group only
                    gflag = 1;
                    break;
                case 'n':  // Names
                    nflag = 1;
                    break;
                case 'r':  // Real IDs
                    rflag = 1;
                    break;
                case 'u':  // User only
                    uflag = 1;
                    break;
                default:
                    printf(2, "id: invalid option -- '%c'\n", *p);
                    usage();
                }
                p++;
            }
        } else {
            // Username argument
            if (username) {
                printf(2, "id: too many arguments\n");
                usage();
            }
            username = argv[i];
        }
    }
    
    // Check for conflicting options
    int exclusive_count = 0;
    if (Gflag) exclusive_count++;
    if (gflag) exclusive_count++;
    if (uflag) exclusive_count++;
    
    if (exclusive_count > 1) {
        printf(2, "id: cannot combine -G, -g, -u\n");
        usage();
    }
    
    // Get IDs for specified user or current process
    if (username) {
        // Look up user
        uid_t uid = get_uid(username);
        if (uid == (uid_t)-1) {
            printf(2, "id: '%s': no such user\n", username);
            exit(1);
        }
        // Set IDs based on username
        ruid = euid = uid;
        rgid = egid = 100;  // Default group
        groups[0] = 100;
        ngroups = 1;
    } else {
        // Get current process IDs
        get_process_ids(&ruid, &euid, &rgid, &egid, groups, &ngroups);
    }
    
    // Print requested information
    if (uflag) {
        // Print user ID only
        uid_t uid = rflag ? ruid : euid;
        print_uid(uid, nflag);
        printf(1, "\n");
    } else if (gflag) {
        // Print group ID only
        gid_t gid = rflag ? rgid : egid;
        print_gid(gid, nflag);
        printf(1, "\n");
    } else if (Gflag) {
        // Print all groups
        print_groups(groups, ngroups, nflag);
        printf(1, "\n");
    } else {
        // Print full information (default)
        print_full_id(ruid, euid, rgid, egid, groups, ngroups);
    }
    
    exit(0);
}