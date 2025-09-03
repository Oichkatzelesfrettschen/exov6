/**
 * user.c - User and group management for FeuerBird LibOS
 * 
 * Implements POSIX-2024 user/group management with capability-based
 * access control and modern security features.
 */

#include "types.h"
#include "defs.h"
#include "param.h"
#include "proc.h"
#include "libos/posix.h"
#include "exo.h"
#include "errno.h"
#include <pwd.h>
#include <grp.h>
#include <shadow.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>

// User database paths
#define PASSWD_FILE "/etc/passwd"
#define GROUP_FILE "/etc/group"
#define SHADOW_FILE "/etc/shadow"

// Maximum limits
#define MAX_USERS 65536
#define MAX_GROUPS 65536
#define NGROUPS_MAX 65536
#define LOGIN_NAME_MAX 256

// User database entry
typedef struct user_entry {
    uid_t uid;
    gid_t gid;
    char username[LOGIN_NAME_MAX];
    char password[128];  // Hashed
    char gecos[256];     // User information
    char home[PATH_MAX];
    char shell[PATH_MAX];
    time_t last_changed;
    int min_days;
    int max_days;
    int warn_days;
    int inactive_days;
    time_t expire_date;
} user_entry_t;

// Group database entry
typedef struct group_entry {
    gid_t gid;
    char groupname[LOGIN_NAME_MAX];
    char password[128];  // Group password (rarely used)
    uid_t *members;
    int nmembers;
} group_entry_t;

// User/group database (in-memory cache)
static user_entry_t *user_db = NULL;
static int user_count = 0;
static group_entry_t *group_db = NULL;
static int group_count = 0;
static struct spinlock user_db_lock;
static int db_initialized = 0;

// Current process credentials (thread-local)
__thread uid_t current_uid = 0;
__thread uid_t current_euid = 0;
__thread uid_t current_suid = 0;
__thread gid_t current_gid = 0;
__thread gid_t current_egid = 0;
__thread gid_t current_sgid = 0;
__thread gid_t current_groups[NGROUPS_MAX];
__thread int current_ngroups = 0;

// Initialize user database
static void
init_user_db(void)
{
    if (db_initialized)
        return;
    
    initlock(&user_db_lock, "userdb");
    
    // Load user database from file
    load_passwd_file();
    load_group_file();
    load_shadow_file();
    
    db_initialized = 1;
}

// Load /etc/passwd
static void
load_passwd_file(void)
{
    FILE *fp;
    char line[1024];
    
    fp = fopen(PASSWD_FILE, "r");
    if (fp == NULL) {
        // Create default users if file doesn't exist
        create_default_users();
        return;
    }
    
    // Allocate initial database
    user_db = malloc(sizeof(user_entry_t) * MAX_USERS);
    user_count = 0;
    
    while (fgets(line, sizeof(line), fp) != NULL) {
        user_entry_t *user = &user_db[user_count];
        char *fields[7];
        int i = 0;
        
        // Parse passwd line: username:password:uid:gid:gecos:home:shell
        char *token = strtok(line, ":");
        while (token != NULL && i < 7) {
            fields[i++] = token;
            token = strtok(NULL, ":");
        }
        
        if (i < 7)
            continue;
        
        strncpy(user->username, fields[0], LOGIN_NAME_MAX - 1);
        strncpy(user->password, fields[1], 127);
        user->uid = atoi(fields[2]);
        user->gid = atoi(fields[3]);
        strncpy(user->gecos, fields[4], 255);
        strncpy(user->home, fields[5], PATH_MAX - 1);
        strncpy(user->shell, fields[6], PATH_MAX - 1);
        
        // Remove newline from shell
        char *nl = strchr(user->shell, '\n');
        if (nl) *nl = '\0';
        
        user_count++;
        if (user_count >= MAX_USERS)
            break;
    }
    
    fclose(fp);
}

// Create default users
static void
create_default_users(void)
{
    user_db = malloc(sizeof(user_entry_t) * MAX_USERS);
    user_count = 0;
    
    // Root user
    user_entry_t *root = &user_db[user_count++];
    root->uid = 0;
    root->gid = 0;
    strcpy(root->username, "root");
    strcpy(root->password, "x");  // Password in shadow file
    strcpy(root->gecos, "System Administrator");
    strcpy(root->home, "/root");
    strcpy(root->shell, "/bin/sh");
    
    // Nobody user
    user_entry_t *nobody = &user_db[user_count++];
    nobody->uid = 65534;
    nobody->gid = 65534;
    strcpy(nobody->username, "nobody");
    strcpy(nobody->password, "x");
    strcpy(nobody->gecos, "Nobody");
    strcpy(nobody->home, "/nonexistent");
    strcpy(nobody->shell, "/bin/false");
}

// Find user by UID
static user_entry_t *
find_user_by_uid(uid_t uid)
{
    init_user_db();
    
    acquire(&user_db_lock);
    for (int i = 0; i < user_count; i++) {
        if (user_db[i].uid == uid) {
            release(&user_db_lock);
            return &user_db[i];
        }
    }
    release(&user_db_lock);
    return NULL;
}

// Find user by name
static user_entry_t *
find_user_by_name(const char *username)
{
    init_user_db();
    
    acquire(&user_db_lock);
    for (int i = 0; i < user_count; i++) {
        if (strcmp(user_db[i].username, username) == 0) {
            release(&user_db_lock);
            return &user_db[i];
        }
    }
    release(&user_db_lock);
    return NULL;
}

/**
 * User ID functions
 */

uid_t
libos_getuid(void)
{
    return current_uid;
}

uid_t
libos_geteuid(void)
{
    return current_euid;
}

int
libos_setuid(uid_t uid)
{
    // Check if we're root or setting to real/saved UID
    if (current_euid != 0 && uid != current_uid && uid != current_suid) {
        errno = EPERM;
        return -1;
    }
    
    // Verify UID exists
    if (find_user_by_uid(uid) == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    // If root, set all UIDs
    if (current_euid == 0) {
        current_uid = uid;
        current_euid = uid;
        current_suid = uid;
    } else {
        current_euid = uid;
    }
    
    // Update capability
    exo_cap user_cap = exo_get_user_cap();
    exo_set_user_id(user_cap, uid);
    
    return 0;
}

int
libos_seteuid(uid_t uid)
{
    // Check permission
    if (uid != current_uid && uid != current_suid && current_euid != 0) {
        errno = EPERM;
        return -1;
    }
    
    // Verify UID exists
    if (find_user_by_uid(uid) == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    current_euid = uid;
    
    // Update capability
    exo_cap user_cap = exo_get_user_cap();
    exo_set_effective_user_id(user_cap, uid);
    
    return 0;
}

int
libos_setreuid(uid_t ruid, uid_t euid)
{
    uid_t old_ruid = current_uid;
    uid_t old_euid = current_euid;
    
    // -1 means don't change
    if (ruid == (uid_t)-1)
        ruid = current_uid;
    if (euid == (uid_t)-1)
        euid = current_euid;
    
    // Permission checks
    if (current_euid != 0) {
        if (ruid != current_uid && ruid != current_euid) {
            errno = EPERM;
            return -1;
        }
        if (euid != current_uid && euid != current_euid && euid != current_suid) {
            errno = EPERM;
            return -1;
        }
    }
    
    // Verify UIDs exist
    if (find_user_by_uid(ruid) == NULL || find_user_by_uid(euid) == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    // Set new values
    current_uid = ruid;
    current_euid = euid;
    
    // Update saved UID if real UID changed
    if (ruid != old_ruid || (euid != old_euid && current_uid != 0)) {
        current_suid = current_euid;
    }
    
    return 0;
}

int
libos_setresuid(uid_t ruid, uid_t euid, uid_t suid)
{
    // Permission checks
    if (current_euid != 0) {
        if ((ruid != (uid_t)-1 && ruid != current_uid && 
             ruid != current_euid && ruid != current_suid) ||
            (euid != (uid_t)-1 && euid != current_uid && 
             euid != current_euid && euid != current_suid) ||
            (suid != (uid_t)-1 && suid != current_uid && 
             suid != current_euid && suid != current_suid)) {
            errno = EPERM;
            return -1;
        }
    }
    
    // Apply changes
    if (ruid != (uid_t)-1)
        current_uid = ruid;
    if (euid != (uid_t)-1)
        current_euid = euid;
    if (suid != (uid_t)-1)
        current_suid = suid;
    
    return 0;
}

int
libos_getresuid(uid_t *ruid, uid_t *euid, uid_t *suid)
{
    if (ruid)
        *ruid = current_uid;
    if (euid)
        *euid = current_euid;
    if (suid)
        *suid = current_suid;
    return 0;
}

/**
 * Group ID functions
 */

gid_t
libos_getgid(void)
{
    return current_gid;
}

gid_t
libos_getegid(void)
{
    return current_egid;
}

int
libos_setgid(gid_t gid)
{
    // Check if we're root or setting to real/saved GID
    if (current_euid != 0 && gid != current_gid && gid != current_sgid) {
        errno = EPERM;
        return -1;
    }
    
    // Verify GID exists
    if (find_group_by_gid(gid) == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    // If root, set all GIDs
    if (current_euid == 0) {
        current_gid = gid;
        current_egid = gid;
        current_sgid = gid;
    } else {
        current_egid = gid;
    }
    
    return 0;
}

int
libos_setegid(gid_t gid)
{
    // Check permission
    if (gid != current_gid && gid != current_sgid && current_euid != 0) {
        errno = EPERM;
        return -1;
    }
    
    // Verify GID exists
    if (find_group_by_gid(gid) == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    current_egid = gid;
    return 0;
}

int
libos_setregid(gid_t rgid, gid_t egid)
{
    gid_t old_rgid = current_gid;
    gid_t old_egid = current_egid;
    
    // -1 means don't change
    if (rgid == (gid_t)-1)
        rgid = current_gid;
    if (egid == (gid_t)-1)
        egid = current_egid;
    
    // Permission checks
    if (current_euid != 0) {
        if (rgid != current_gid && rgid != current_egid) {
            errno = EPERM;
            return -1;
        }
        if (egid != current_gid && egid != current_egid && egid != current_sgid) {
            errno = EPERM;
            return -1;
        }
    }
    
    // Set new values
    current_gid = rgid;
    current_egid = egid;
    
    // Update saved GID if real GID changed
    if (rgid != old_rgid || (egid != old_egid && current_uid != 0)) {
        current_sgid = current_egid;
    }
    
    return 0;
}

int
libos_setresgid(gid_t rgid, gid_t egid, gid_t sgid)
{
    // Permission checks
    if (current_euid != 0) {
        if ((rgid != (gid_t)-1 && rgid != current_gid && 
             rgid != current_egid && rgid != current_sgid) ||
            (egid != (gid_t)-1 && egid != current_gid && 
             egid != current_egid && egid != current_sgid) ||
            (sgid != (gid_t)-1 && sgid != current_gid && 
             sgid != current_egid && sgid != current_sgid)) {
            errno = EPERM;
            return -1;
        }
    }
    
    // Apply changes
    if (rgid != (gid_t)-1)
        current_gid = rgid;
    if (egid != (gid_t)-1)
        current_egid = egid;
    if (sgid != (gid_t)-1)
        current_sgid = sgid;
    
    return 0;
}

int
libos_getresgid(gid_t *rgid, gid_t *egid, gid_t *sgid)
{
    if (rgid)
        *rgid = current_gid;
    if (egid)
        *egid = current_egid;
    if (sgid)
        *sgid = current_sgid;
    return 0;
}

/**
 * Supplementary groups
 */

int
libos_getgroups(int size, gid_t list[])
{
    if (size < 0) {
        errno = EINVAL;
        return -1;
    }
    
    if (size == 0) {
        // Return number of groups
        return current_ngroups;
    }
    
    if (size < current_ngroups) {
        errno = EINVAL;
        return -1;
    }
    
    // Copy groups
    for (int i = 0; i < current_ngroups; i++) {
        list[i] = current_groups[i];
    }
    
    return current_ngroups;
}

int
libos_setgroups(size_t size, const gid_t *list)
{
    // Only root can set groups
    if (current_euid != 0) {
        errno = EPERM;
        return -1;
    }
    
    if (size > NGROUPS_MAX) {
        errno = EINVAL;
        return -1;
    }
    
    // Verify all groups exist
    for (size_t i = 0; i < size; i++) {
        if (find_group_by_gid(list[i]) == NULL) {
            errno = EINVAL;
            return -1;
        }
    }
    
    // Set new groups
    current_ngroups = size;
    for (size_t i = 0; i < size; i++) {
        current_groups[i] = list[i];
    }
    
    return 0;
}

int
libos_initgroups(const char *user, gid_t group)
{
    user_entry_t *u;
    gid_t groups[NGROUPS_MAX];
    int ngroups = 0;
    
    // Only root can call initgroups
    if (current_euid != 0) {
        errno = EPERM;
        return -1;
    }
    
    // Find user
    u = find_user_by_name(user);
    if (u == NULL) {
        errno = EINVAL;
        return -1;
    }
    
    // Add primary group
    groups[ngroups++] = group;
    
    // Add supplementary groups from group database
    acquire(&user_db_lock);
    for (int i = 0; i < group_count && ngroups < NGROUPS_MAX; i++) {
        group_entry_t *g = &group_db[i];
        for (int j = 0; j < g->nmembers; j++) {
            if (g->members[j] == u->uid) {
                // Check if not already added
                int found = 0;
                for (int k = 0; k < ngroups; k++) {
                    if (groups[k] == g->gid) {
                        found = 1;
                        break;
                    }
                }
                if (!found) {
                    groups[ngroups++] = g->gid;
                }
                break;
            }
        }
    }
    release(&user_db_lock);
    
    return libos_setgroups(ngroups, groups);
}

/**
 * User database access
 */

struct passwd *
libos_getpwuid(uid_t uid)
{
    static struct passwd pwd;
    user_entry_t *u;
    
    u = find_user_by_uid(uid);
    if (u == NULL) {
        return NULL;
    }
    
    // Fill passwd structure
    pwd.pw_name = u->username;
    pwd.pw_passwd = u->password;
    pwd.pw_uid = u->uid;
    pwd.pw_gid = u->gid;
    pwd.pw_gecos = u->gecos;
    pwd.pw_dir = u->home;
    pwd.pw_shell = u->shell;
    
    return &pwd;
}

struct passwd *
libos_getpwnam(const char *name)
{
    static struct passwd pwd;
    user_entry_t *u;
    
    u = find_user_by_name(name);
    if (u == NULL) {
        return NULL;
    }
    
    // Fill passwd structure
    pwd.pw_name = u->username;
    pwd.pw_passwd = u->password;
    pwd.pw_uid = u->uid;
    pwd.pw_gid = u->gid;
    pwd.pw_gecos = u->gecos;
    pwd.pw_dir = u->home;
    pwd.pw_shell = u->shell;
    
    return &pwd;
}

/**
 * Login name
 */

char *
libos_getlogin(void)
{
    static char login[LOGIN_NAME_MAX];
    user_entry_t *u;
    
    u = find_user_by_uid(current_uid);
    if (u == NULL) {
        return NULL;
    }
    
    strncpy(login, u->username, LOGIN_NAME_MAX - 1);
    login[LOGIN_NAME_MAX - 1] = '\0';
    
    return login;
}

int
libos_getlogin_r(char *name, size_t namesize)
{
    user_entry_t *u;
    
    if (name == NULL || namesize == 0) {
        errno = EINVAL;
        return -1;
    }
    
    u = find_user_by_uid(current_uid);
    if (u == NULL) {
        errno = ENXIO;
        return -1;
    }
    
    if (strlen(u->username) >= namesize) {
        errno = ERANGE;
        return -1;
    }
    
    strncpy(name, u->username, namesize - 1);
    name[namesize - 1] = '\0';
    
    return 0;
}

/**
 * Access control
 */

int
libos_access(const char *pathname, int mode)
{
    struct stat st;
    int granted = 0;
    
    // Get file information
    if (stat(pathname, &st) < 0) {
        return -1;  // errno set by stat
    }
    
    // F_OK - just check existence
    if (mode == F_OK) {
        return 0;
    }
    
    // Root can access anything (except execute needs at least one x bit)
    if (current_euid == 0) {
        if (mode & X_OK) {
            if (st.st_mode & (S_IXUSR | S_IXGRP | S_IXOTH)) {
                return 0;
            }
            errno = EACCES;
            return -1;
        }
        return 0;
    }
    
    // Check owner permissions
    if (st.st_uid == current_euid) {
        if ((mode & R_OK) && !(st.st_mode & S_IRUSR))
            goto denied;
        if ((mode & W_OK) && !(st.st_mode & S_IWUSR))
            goto denied;
        if ((mode & X_OK) && !(st.st_mode & S_IXUSR))
            goto denied;
        return 0;
    }
    
    // Check group permissions
    if (st.st_gid == current_egid || in_group(st.st_gid)) {
        if ((mode & R_OK) && !(st.st_mode & S_IRGRP))
            goto denied;
        if ((mode & W_OK) && !(st.st_mode & S_IWGRP))
            goto denied;
        if ((mode & X_OK) && !(st.st_mode & S_IXGRP))
            goto denied;
        return 0;
    }
    
    // Check other permissions
    if ((mode & R_OK) && !(st.st_mode & S_IROTH))
        goto denied;
    if ((mode & W_OK) && !(st.st_mode & S_IWOTH))
        goto denied;
    if ((mode & X_OK) && !(st.st_mode & S_IXOTH))
        goto denied;
    
    return 0;
    
denied:
    errno = EACCES;
    return -1;
}

// Check if current user is in specified group
static int
in_group(gid_t gid)
{
    for (int i = 0; i < current_ngroups; i++) {
        if (current_groups[i] == gid) {
            return 1;
        }
    }
    return 0;
}