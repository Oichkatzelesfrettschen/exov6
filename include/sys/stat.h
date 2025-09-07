#pragma once

/**
 * @file sys/stat.h
 * @brief File status and mode definitions
 */

#include <sys/types.h>
#include <stdint.h>

// File type macros
#define S_IFMT   0170000  // File type mask
#define S_IFREG  0100000  // Regular file
#define S_IFDIR  0040000  // Directory
#define S_IFCHR  0020000  // Character device
#define S_IFBLK  0060000  // Block device
#define S_IFIFO  0010000  // FIFO
#define S_IFLNK  0120000  // Symbolic link
#define S_IFSOCK 0140000  // Socket

// File mode bits
#define S_ISUID  0004000  // Set UID
#define S_ISGID  0002000  // Set GID
#define S_ISVTX  0001000  // Sticky bit

// User permissions
#define S_IRUSR  0000400  // User read
#define S_IWUSR  0000200  // User write
#define S_IXUSR  0000100  // User execute
#define S_IRWXU  0000700  // User all

// Group permissions
#define S_IRGRP  0000040  // Group read
#define S_IWGRP  0000020  // Group write
#define S_IXGRP  0000010  // Group execute
#define S_IRWXG  0000070  // Group all

// Other permissions
#define S_IROTH  0000004  // Other read
#define S_IWOTH  0000002  // Other write
#define S_IXOTH  0000001  // Other execute
#define S_IRWXO  0000007  // Other all

// File type test macros
#define S_ISREG(m)  (((m) & S_IFMT) == S_IFREG)
#define S_ISDIR(m)  (((m) & S_IFMT) == S_IFDIR)
#define S_ISCHR(m)  (((m) & S_IFMT) == S_IFCHR)
#define S_ISBLK(m)  (((m) & S_IFMT) == S_IFBLK)
#define S_ISFIFO(m) (((m) & S_IFMT) == S_IFIFO)
#define S_ISLNK(m)  (((m) & S_IFMT) == S_IFLNK)
#define S_ISSOCK(m) (((m) & S_IFMT) == S_IFSOCK)

struct stat {
    dev_t     st_dev;     // Device ID
    ino_t     st_ino;     // Inode number
    mode_t    st_mode;    // File mode
    nlink_t   st_nlink;   // Number of hard links
    uid_t     st_uid;     // User ID
    gid_t     st_gid;     // Group ID
    dev_t     st_rdev;    // Device ID (if special file)
    off_t     st_size;    // File size
    blksize_t st_blksize; // Block size
    blkcnt_t  st_blkcnt;  // Number of blocks
    time_t    st_atime;   // Access time
    time_t    st_mtime;   // Modification time
    time_t    st_ctime;   // Change time
};

// Function declarations
int stat(const char* pathname, struct stat* statbuf);
int fstat(int fd, struct stat* statbuf);
int lstat(const char* pathname, struct stat* statbuf);
int mkdir(const char* pathname, mode_t mode);
int chmod(const char* pathname, mode_t mode);
int fchmod(int fd, mode_t mode);
mode_t umask(mode_t mask);