/**
 * @file libfs_stubs.c
 * @brief LibFS stub implementations for unified build
 * 
 * C17 compliant stubs to enable libos compilation.
 * These will be replaced with full implementations.
 */

#include <sys/types.h>
#include <sys/stat.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>
#include "file.h"
#include "libfs.h"
#include "exo.h"

// Stub file structure for minimal functionality
static struct file dummy_files[32];
static int next_file_idx = 0;

struct file* libfs_open(const char* path, int flags) {
    (void)path; (void)flags;
    if (next_file_idx >= 32) return NULL;
    
    struct file* f = &dummy_files[next_file_idx++];
    f->type = FD_INODE;
    f->ref = 1;
    f->readable = 1;
    f->writable = 1;
    f->off = 0;
    f->flags = flags;
    return f;
}

int libfs_read(struct file* f, void* buf, size_t count) {
    (void)f; (void)buf; (void)count;
    return 0;  // EOF
}

int libfs_write(struct file* f, const void* buf, size_t count) {
    (void)f; (void)buf;
    return (int)count;  // Pretend success
}

int libfs_truncate(struct file* f, size_t length) {
    (void)f; (void)length;
    return 0;
}

int libfs_close(struct file* f) {
    if (f && f->ref > 0) {
        f->ref--;
        return 0;
    }
    return -1;
}

int fileclose(struct file* f) {
    return libfs_close(f);
}

int filestat(struct file* f, struct stat* st) {
    (void)f;
    if (!st) return -1;
    
    // Fill with dummy values
    st->st_dev = 1;
    st->st_ino = 1;
    st->st_mode = S_IFREG | 0644;
    st->st_nlink = 1;
    st->st_uid = 0;
    st->st_gid = 0;
    st->st_rdev = 0;
    st->st_size = 0;
    st->st_blksize = 512;
    st->st_blkcnt = 0;
    st->st_atime = 0;
    st->st_mtime = 0;
    st->st_ctime = 0;
    
    return 0;
}

int libfs_unlink(const char* path) {
    (void)path;
    return 0;  // Pretend success
}

int libfs_rename(const char* oldpath, const char* newpath) {
    (void)oldpath; (void)newpath;
    return 0;  // Pretend success
}

int libfs_mkdir(const char* path) {
    (void)path;
    return 0;  // Pretend success
}

// Additional stubs for posix.c
struct file* filedup(struct file* f) {
    if (!f) return NULL;
    f->ref++;
    return f;
}

int sigcheck(void) {
    return 0;  // No signals pending
}

int sigsend(int pgrp, int sig) {
    (void)pgrp; (void)sig;
    return 0;  // Pretend success
}

// Exokernel proper implementations
int exo_yield_to(exo_cap target) {
    // Validate the capability before yielding
    if (!cap_verify(target)) {
        return -1;  // Invalid capability
    }
    
    // For now, treat all valid capabilities as scheduler endpoints
    // In full implementation, this would transfer control to target
    return exo_yield();  // Fallback to general yield
}

// POSIX stubs
int usleep(useconds_t usec) {
    (void)usec;
    return 0;  // Pretend to sleep
}

// Pthread capability management - proper implementation
exo_cap pthread_get_scheduler_cap(pthread_t thread) {
    // Create a proper scheduler capability for the thread
    // In full implementation, this would look up thread's scheduler assignment
    exo_cap sched_cap = cap_new(
        (uint32_t)thread,                    // Use thread ID as resource ID
        EXO_RIGHT_EXEC | EXO_RIGHT_CTL,     // Execution and control rights
        (uint32_t)getpid()                   // Current process owns the capability
    );
    
    return sched_cap;
}