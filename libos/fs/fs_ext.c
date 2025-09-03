/**
 * fs_ext.c - Extended File System Operations for LibOS
 * 
 * Implements POSIX-2024 compliant file system extensions including:
 * - Permission management (chmod, chown)
 * - Access control (access, umask)
 * - Extended attributes
 * - File status operations
 * 
 * Part of the FeuerBird LibOS exokernel implementation
 */

#include "types.h"
#include "defs.h"
#include "param.h"
#include "stat.h"
#include "mmu.h"
#include "proc.h"
#include "fs.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "file.h"
#include "fcntl.h"
#include "syscall.h"
#include "libos.h"
#include <errno.h>

// Process umask value (thread-local in multi-threaded environments)
static _Thread_local mode_t process_umask = 022;  // Default umask

// Permission checking cache for performance
typedef struct {
    uint32_t ino;      // Inode number
    uid_t uid;         // User ID
    gid_t gid;         // Group ID
    mode_t mode;       // Cached permissions
    uint64_t expires;  // Cache expiration time
} perm_cache_t;

#define PERM_CACHE_SIZE 64
static perm_cache_t perm_cache[PERM_CACHE_SIZE];
static struct spinlock perm_cache_lock;

// Extended attribute storage
typedef struct xattr {
    char name[64];     // Attribute name
    void *value;       // Attribute value
    size_t size;       // Value size
    struct xattr *next;
} xattr_t;

// Extended attributes per inode
static struct {
    uint32_t ino;
    xattr_t *attrs;
    struct spinlock lock;
} xattr_table[NINODE];

/**
 * Initialize file system extensions
 */
void
libos_fs_ext_init(void)
{
    initlock(&perm_cache_lock, "perm_cache");
    
    // Initialize xattr table locks
    for (int i = 0; i < NINODE; i++) {
        initlock(&xattr_table[i].lock, "xattr");
        xattr_table[i].ino = 0;
        xattr_table[i].attrs = 0;
    }
    
    // Clear permission cache
    memset(perm_cache, 0, sizeof(perm_cache));
}

/**
 * Set file permissions (chmod)
 * 
 * @param path File path
 * @param mode New permission mode
 * @return 0 on success, -1 on error with errno set
 */
int
libos_chmod(const char *path, mode_t mode)
{
    struct inode *ip;
    
    // Validate mode (keep only permission bits)
    mode &= 07777;
    
    // Get inode
    if ((ip = namei(path)) == 0) {
        errno = ENOENT;
        return -1;
    }
    
    ilock(ip);
    
    // Check if caller owns the file or is root
    struct proc *p = myproc();
    if (p->uid != 0 && p->uid != ip->uid) {
        iunlockput(ip);
        errno = EPERM;
        return -1;
    }
    
    // Update mode
    ip->mode = (ip->mode & ~07777) | mode;
    iupdate(ip);
    
    // Invalidate permission cache for this inode
    acquire(&perm_cache_lock);
    for (int i = 0; i < PERM_CACHE_SIZE; i++) {
        if (perm_cache[i].ino == ip->inum) {
            perm_cache[i].expires = 0;
        }
    }
    release(&perm_cache_lock);
    
    iunlockput(ip);
    return 0;
}

/**
 * Set file permissions by file descriptor (fchmod)
 * 
 * @param fd File descriptor
 * @param mode New permission mode
 * @return 0 on success, -1 on error with errno set
 */
int
libos_fchmod(int fd, mode_t mode)
{
    struct file *f;
    struct proc *p = myproc();
    
    // Validate file descriptor
    if (fd < 0 || fd >= NOFILE || (f = p->ofile[fd]) == 0) {
        errno = EBADF;
        return -1;
    }
    
    // Must be a regular file or directory
    if (f->type != FD_INODE) {
        errno = EINVAL;
        return -1;
    }
    
    struct inode *ip = f->ip;
    ilock(ip);
    
    // Check permissions
    if (p->uid != 0 && p->uid != ip->uid) {
        iunlock(ip);
        errno = EPERM;
        return -1;
    }
    
    // Update mode
    mode &= 07777;
    ip->mode = (ip->mode & ~07777) | mode;
    iupdate(ip);
    
    // Invalidate cache
    acquire(&perm_cache_lock);
    for (int i = 0; i < PERM_CACHE_SIZE; i++) {
        if (perm_cache[i].ino == ip->inum) {
            perm_cache[i].expires = 0;
        }
    }
    release(&perm_cache_lock);
    
    iunlock(ip);
    return 0;
}

/**
 * Change file ownership (chown)
 * 
 * @param path File path
 * @param owner New owner UID
 * @param group New group GID
 * @return 0 on success, -1 on error with errno set
 */
int
libos_chown(const char *path, uid_t owner, gid_t group)
{
    struct inode *ip;
    struct proc *p = myproc();
    
    // Get inode
    if ((ip = namei(path)) == 0) {
        errno = ENOENT;
        return -1;
    }
    
    ilock(ip);
    
    // Only root can change ownership
    if (p->uid != 0) {
        // Non-root can only change group if they own the file
        // and are a member of the target group
        if (owner != (uid_t)-1 || p->uid != ip->uid) {
            iunlockput(ip);
            errno = EPERM;
            return -1;
        }
        
        // Check group membership
        if (group != (gid_t)-1) {
            int is_member = (p->gid == group);
            for (int i = 0; i < p->ngroups && !is_member; i++) {
                if (p->groups[i] == group) {
                    is_member = 1;
                }
            }
            if (!is_member) {
                iunlockput(ip);
                errno = EPERM;
                return -1;
            }
        }
    }
    
    // Update ownership
    if (owner != (uid_t)-1) {
        ip->uid = owner;
    }
    if (group != (gid_t)-1) {
        ip->gid = group;
    }
    
    // Clear setuid/setgid bits on ownership change (security)
    if (p->uid != 0) {
        ip->mode &= ~(S_ISUID | S_ISGID);
    }
    
    iupdate(ip);
    
    // Invalidate permission cache
    acquire(&perm_cache_lock);
    for (int i = 0; i < PERM_CACHE_SIZE; i++) {
        if (perm_cache[i].ino == ip->inum) {
            perm_cache[i].expires = 0;
        }
    }
    release(&perm_cache_lock);
    
    iunlockput(ip);
    return 0;
}

/**
 * Change file ownership by file descriptor (fchown)
 * 
 * @param fd File descriptor
 * @param owner New owner UID
 * @param group New group GID
 * @return 0 on success, -1 on error with errno set
 */
int
libos_fchown(int fd, uid_t owner, gid_t group)
{
    struct file *f;
    struct proc *p = myproc();
    
    // Validate file descriptor
    if (fd < 0 || fd >= NOFILE || (f = p->ofile[fd]) == 0) {
        errno = EBADF;
        return -1;
    }
    
    if (f->type != FD_INODE) {
        errno = EINVAL;
        return -1;
    }
    
    struct inode *ip = f->ip;
    ilock(ip);
    
    // Permission checks (same as chown)
    if (p->uid != 0) {
        if (owner != (uid_t)-1 || p->uid != ip->uid) {
            iunlock(ip);
            errno = EPERM;
            return -1;
        }
        
        if (group != (gid_t)-1) {
            int is_member = (p->gid == group);
            for (int i = 0; i < p->ngroups && !is_member; i++) {
                if (p->groups[i] == group) {
                    is_member = 1;
                }
            }
            if (!is_member) {
                iunlock(ip);
                errno = EPERM;
                return -1;
            }
        }
    }
    
    // Update ownership
    if (owner != (uid_t)-1) {
        ip->uid = owner;
    }
    if (group != (gid_t)-1) {
        ip->gid = group;
    }
    
    // Clear setuid/setgid bits
    if (p->uid != 0) {
        ip->mode &= ~(S_ISUID | S_ISGID);
    }
    
    iupdate(ip);
    
    // Invalidate cache
    acquire(&perm_cache_lock);
    for (int i = 0; i < PERM_CACHE_SIZE; i++) {
        if (perm_cache[i].ino == ip->inum) {
            perm_cache[i].expires = 0;
        }
    }
    release(&perm_cache_lock);
    
    iunlock(ip);
    return 0;
}

/**
 * Check file access permissions
 * 
 * @param path File path
 * @param mode Access mode to check (R_OK, W_OK, X_OK, F_OK)
 * @return 0 if access allowed, -1 if not with errno set
 */
int
libos_access(const char *path, int mode)
{
    struct inode *ip;
    struct proc *p = myproc();
    int ret = 0;
    
    // Get inode
    if ((ip = namei(path)) == 0) {
        errno = ENOENT;
        return -1;
    }
    
    ilock(ip);
    
    // F_OK just checks existence
    if (mode == F_OK) {
        iunlock(ip);
        iput(ip);
        return 0;
    }
    
    // Check for cached permission
    uint32_t cache_key = ip->inum % PERM_CACHE_SIZE;
    acquire(&perm_cache_lock);
    if (perm_cache[cache_key].ino == ip->inum &&
        perm_cache[cache_key].uid == p->uid &&
        perm_cache[cache_key].gid == p->gid &&
        perm_cache[cache_key].expires > ticks) {
        mode_t cached_mode = perm_cache[cache_key].mode;
        release(&perm_cache_lock);
        
        // Check cached permissions
        if ((mode & R_OK) && !(cached_mode & S_IRUSR)) ret = -1;
        if ((mode & W_OK) && !(cached_mode & S_IWUSR)) ret = -1;
        if ((mode & X_OK) && !(cached_mode & S_IXUSR)) ret = -1;
        
        iunlock(ip);
        iput(ip);
        if (ret < 0) errno = EACCES;
        return ret;
    }
    release(&perm_cache_lock);
    
    // Root has all access (except execute on non-executable files)
    if (p->uid == 0) {
        if ((mode & X_OK) && !(ip->mode & 0111)) {
            ret = -1;
            errno = EACCES;
        }
    } else {
        // Determine which permission bits to check
        mode_t check_mode = 0;
        
        if (p->uid == ip->uid) {
            // Owner permissions
            if (mode & R_OK) check_mode |= S_IRUSR;
            if (mode & W_OK) check_mode |= S_IWUSR;
            if (mode & X_OK) check_mode |= S_IXUSR;
        } else {
            // Check group membership
            int is_group_member = (p->gid == ip->gid);
            for (int i = 0; i < p->ngroups && !is_group_member; i++) {
                if (p->groups[i] == ip->gid) {
                    is_group_member = 1;
                }
            }
            
            if (is_group_member) {
                // Group permissions
                if (mode & R_OK) check_mode |= S_IRGRP;
                if (mode & W_OK) check_mode |= S_IWGRP;
                if (mode & X_OK) check_mode |= S_IXGRP;
            } else {
                // Other permissions
                if (mode & R_OK) check_mode |= S_IROTH;
                if (mode & W_OK) check_mode |= S_IWOTH;
                if (mode & X_OK) check_mode |= S_IXOTH;
            }
        }
        
        // Check if all requested permissions are granted
        if ((ip->mode & check_mode) != check_mode) {
            ret = -1;
            errno = EACCES;
        }
    }
    
    // Update cache on success
    if (ret == 0) {
        acquire(&perm_cache_lock);
        perm_cache[cache_key].ino = ip->inum;
        perm_cache[cache_key].uid = p->uid;
        perm_cache[cache_key].gid = p->gid;
        perm_cache[cache_key].mode = ip->mode;
        perm_cache[cache_key].expires = ticks + 100;  // Cache for 1 second
        release(&perm_cache_lock);
    }
    
    iunlock(ip);
    iput(ip);
    return ret;
}

/**
 * Get process file creation mask
 * 
 * @return Current umask value
 */
mode_t
libos_umask(mode_t mask)
{
    mode_t old_mask = process_umask;
    process_umask = mask & 07777;
    return old_mask;
}

/**
 * Get current umask value (non-modifying)
 * 
 * @return Current umask
 */
mode_t
libos_get_umask(void)
{
    return process_umask;
}

/**
 * Apply umask to mode for file creation
 * 
 * @param mode Requested mode
 * @return Mode with umask applied
 */
mode_t
libos_apply_umask(mode_t mode)
{
    return mode & ~process_umask;
}

/**
 * Set extended attribute on file
 * 
 * @param path File path
 * @param name Attribute name
 * @param value Attribute value
 * @param size Value size
 * @param flags Creation flags
 * @return 0 on success, -1 on error with errno set
 */
int
libos_setxattr(const char *path, const char *name, const void *value,
               size_t size, int flags)
{
    struct inode *ip;
    
    // Validate parameters
    if (!name || strlen(name) >= 64) {
        errno = EINVAL;
        return -1;
    }
    
    // Get inode
    if ((ip = namei(path)) == 0) {
        errno = ENOENT;
        return -1;
    }
    
    ilock(ip);
    
    // Check write permission
    struct proc *p = myproc();
    if (p->uid != 0 && p->uid != ip->uid) {
        iunlockput(ip);
        errno = EPERM;
        return -1;
    }
    
    // Find xattr slot for this inode
    int slot = ip->inum % NINODE;
    acquire(&xattr_table[slot].lock);
    
    // Initialize if needed
    if (xattr_table[slot].ino != ip->inum) {
        // Free old attributes
        xattr_t *attr = xattr_table[slot].attrs;
        while (attr) {
            xattr_t *next = attr->next;
            if (attr->value) kfree(attr->value);
            kfree((char*)attr);
            attr = next;
        }
        xattr_table[slot].ino = ip->inum;
        xattr_table[slot].attrs = 0;
    }
    
    // Find existing attribute
    xattr_t *attr = xattr_table[slot].attrs;
    xattr_t *prev = 0;
    while (attr) {
        if (strcmp(attr->name, name) == 0) {
            break;
        }
        prev = attr;
        attr = attr->next;
    }
    
    // Handle flags
    if (attr && (flags & XATTR_CREATE)) {
        release(&xattr_table[slot].lock);
        iunlockput(ip);
        errno = EEXIST;
        return -1;
    }
    if (!attr && (flags & XATTR_REPLACE)) {
        release(&xattr_table[slot].lock);
        iunlockput(ip);
        errno = ENODATA;
        return -1;
    }
    
    // Create or update attribute
    if (!attr) {
        attr = (xattr_t*)kalloc();
        if (!attr) {
            release(&xattr_table[slot].lock);
            iunlockput(ip);
            errno = ENOMEM;
            return -1;
        }
        strncpy(attr->name, name, 63);
        attr->name[63] = 0;
        attr->next = xattr_table[slot].attrs;
        xattr_table[slot].attrs = attr;
    } else {
        // Free old value
        if (attr->value) kfree(attr->value);
    }
    
    // Set new value
    if (size > 0) {
        attr->value = kalloc();
        if (!attr->value) {
            // Remove attribute on allocation failure
            if (prev) prev->next = attr->next;
            else xattr_table[slot].attrs = attr->next;
            kfree((char*)attr);
            
            release(&xattr_table[slot].lock);
            iunlockput(ip);
            errno = ENOMEM;
            return -1;
        }
        memmove(attr->value, value, size);
    } else {
        attr->value = 0;
    }
    attr->size = size;
    
    release(&xattr_table[slot].lock);
    iunlockput(ip);
    return 0;
}

/**
 * Get extended attribute from file
 * 
 * @param path File path
 * @param name Attribute name
 * @param value Buffer for attribute value
 * @param size Buffer size
 * @return Size of attribute value, -1 on error with errno set
 */
ssize_t
libos_getxattr(const char *path, const char *name, void *value, size_t size)
{
    struct inode *ip;
    
    // Validate parameters
    if (!name) {
        errno = EINVAL;
        return -1;
    }
    
    // Get inode
    if ((ip = namei(path)) == 0) {
        errno = ENOENT;
        return -1;
    }
    
    ilock(ip);
    
    // Find xattr
    int slot = ip->inum % NINODE;
    acquire(&xattr_table[slot].lock);
    
    if (xattr_table[slot].ino != ip->inum) {
        release(&xattr_table[slot].lock);
        iunlock(ip);
        iput(ip);
        errno = ENODATA;
        return -1;
    }
    
    xattr_t *attr = xattr_table[slot].attrs;
    while (attr) {
        if (strcmp(attr->name, name) == 0) {
            break;
        }
        attr = attr->next;
    }
    
    if (!attr) {
        release(&xattr_table[slot].lock);
        iunlock(ip);
        iput(ip);
        errno = ENODATA;
        return -1;
    }
    
    // Return size if buffer is NULL
    if (!value) {
        ssize_t ret = attr->size;
        release(&xattr_table[slot].lock);
        iunlock(ip);
        iput(ip);
        return ret;
    }
    
    // Check buffer size
    if (size < attr->size) {
        release(&xattr_table[slot].lock);
        iunlock(ip);
        iput(ip);
        errno = ERANGE;
        return -1;
    }
    
    // Copy value
    if (attr->value && attr->size > 0) {
        memmove(value, attr->value, attr->size);
    }
    
    ssize_t ret = attr->size;
    release(&xattr_table[slot].lock);
    iunlock(ip);
    iput(ip);
    return ret;
}

/**
 * List extended attributes on file
 * 
 * @param path File path
 * @param list Buffer for attribute names
 * @param size Buffer size
 * @return Total size of attribute name list, -1 on error
 */
ssize_t
libos_listxattr(const char *path, char *list, size_t size)
{
    struct inode *ip;
    
    // Get inode
    if ((ip = namei(path)) == 0) {
        errno = ENOENT;
        return -1;
    }
    
    ilock(ip);
    
    int slot = ip->inum % NINODE;
    acquire(&xattr_table[slot].lock);
    
    ssize_t total_size = 0;
    
    if (xattr_table[slot].ino == ip->inum) {
        xattr_t *attr = xattr_table[slot].attrs;
        
        // Calculate total size needed
        while (attr) {
            total_size += strlen(attr->name) + 1;
            attr = attr->next;
        }
        
        // Copy names if buffer provided
        if (list && size > 0) {
            if (size < total_size) {
                release(&xattr_table[slot].lock);
                iunlock(ip);
                iput(ip);
                errno = ERANGE;
                return -1;
            }
            
            attr = xattr_table[slot].attrs;
            char *p = list;
            while (attr) {
                int len = strlen(attr->name) + 1;
                memmove(p, attr->name, len);
                p += len;
                attr = attr->next;
            }
        }
    }
    
    release(&xattr_table[slot].lock);
    iunlock(ip);
    iput(ip);
    return total_size;
}

/**
 * Remove extended attribute from file
 * 
 * @param path File path
 * @param name Attribute name to remove
 * @return 0 on success, -1 on error with errno set
 */
int
libos_removexattr(const char *path, const char *name)
{
    struct inode *ip;
    
    if (!name) {
        errno = EINVAL;
        return -1;
    }
    
    // Get inode
    if ((ip = namei(path)) == 0) {
        errno = ENOENT;
        return -1;
    }
    
    ilock(ip);
    
    // Check permission
    struct proc *p = myproc();
    if (p->uid != 0 && p->uid != ip->uid) {
        iunlockput(ip);
        errno = EPERM;
        return -1;
    }
    
    int slot = ip->inum % NINODE;
    acquire(&xattr_table[slot].lock);
    
    if (xattr_table[slot].ino != ip->inum) {
        release(&xattr_table[slot].lock);
        iunlockput(ip);
        errno = ENODATA;
        return -1;
    }
    
    // Find and remove attribute
    xattr_t *attr = xattr_table[slot].attrs;
    xattr_t *prev = 0;
    
    while (attr) {
        if (strcmp(attr->name, name) == 0) {
            // Remove from list
            if (prev) {
                prev->next = attr->next;
            } else {
                xattr_table[slot].attrs = attr->next;
            }
            
            // Free memory
            if (attr->value) kfree(attr->value);
            kfree((char*)attr);
            
            release(&xattr_table[slot].lock);
            iunlockput(ip);
            return 0;
        }
        prev = attr;
        attr = attr->next;
    }
    
    release(&xattr_table[slot].lock);
    iunlockput(ip);
    errno = ENODATA;
    return -1;
}