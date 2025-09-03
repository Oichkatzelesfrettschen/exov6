# Exokernelized LibC Design Document

## Overview

This document outlines the design and implementation of a POSIX-2024 (SUSv5) compliant C library for the FeuerBird exokernel. Unlike traditional libc implementations that make direct system calls, our exokernelized libc operates through capability-based resource management and user-space policy implementation.

## Architecture

### Three-Layer Design

```
┌─────────────────────────────────────────────┐
│         POSIX Applications                   │
│         (unmodified Unix programs)           │
└─────────────────────────────────────────────┘
                    ↓ POSIX API
┌─────────────────────────────────────────────┐
│         Exokernel LibC (libexoc)            │
│   - POSIX-2024 compliant interfaces         │
│   - Capability translation layer            │
│   - Resource policy implementation          │
└─────────────────────────────────────────────┘
                    ↓ Capability Operations
┌─────────────────────────────────────────────┐
│         Exokernel (kernel/)                 │
│   - Raw hardware multiplexing               │
│   - Capability enforcement                  │
│   - Protected control transfer              │
└─────────────────────────────────────────────┘
```

## Implementation Status

### Completed Components

#### 1. Error Handling (libos/errno.c)
- ✅ Full errno system with 133 POSIX error codes
- ✅ Thread-local storage support
- ✅ strerror() and perror() implementations

#### 2. Signal Handling (libos/signal_posix.c)
- ✅ 31+ POSIX signals defined
- ✅ sigaction, sigprocmask, sigsuspend
- ✅ Signal sets API (sigemptyset, sigfillset, etc.)
- ✅ Real-time signal extensions

#### 3. Threading (libos/pthread_*.c)
- ✅ pthread_create, pthread_join
- ✅ Mutex operations (pthread_mutex_*)
- ✅ Thread-specific data (pthread_key_*)
- ✅ Condition variables (pthread_cond_*)

#### 4. File Operations (libos/file.c, fs.c)
- ✅ Basic open, read, write, close
- ✅ Directory operations (mkdir, rmdir)
- ✅ File status (stat, fstat)
- ⚠️ Missing: chmod, chown, access

### Required Implementations

#### 1. Process Management
```c
// Need to implement in libos/process.c
pid_t fork(void);           // Via exo_fork capability
int execve(const char *path, char *const argv[], char *const envp[]);
pid_t wait(int *status);
pid_t waitpid(pid_t pid, int *status, int options);
void _exit(int status);
pid_t getpid(void);
pid_t getppid(void);
int nice(int inc);
```

#### 2. Memory Management
```c
// Need to implement in libos/memory.c
void *mmap(void *addr, size_t len, int prot, int flags, int fd, off_t off);
int munmap(void *addr, size_t len);
int mprotect(void *addr, size_t len, int prot);
int msync(void *addr, size_t len, int flags);
int mlock(const void *addr, size_t len);
int munlock(const void *addr, size_t len);
```

#### 3. Time Functions
```c
// Need to implement in libos/time.c
time_t time(time_t *t);
int clock_gettime(clockid_t clk_id, struct timespec *tp);
int clock_settime(clockid_t clk_id, const struct timespec *tp);
int nanosleep(const struct timespec *req, struct timespec *rem);
int gettimeofday(struct timeval *tv, struct timezone *tz);
```

#### 4. User/Group Management
```c
// Need to implement in libos/user.c
uid_t getuid(void);
uid_t geteuid(void);
int setuid(uid_t uid);
int seteuid(uid_t uid);
gid_t getgid(void);
gid_t getegid(void);
int setgid(gid_t gid);
int setegid(gid_t gid);
```

#### 5. Terminal I/O
```c
// Partially implemented in libos/termios.c
int tcgetattr(int fd, struct termios *termios_p);
int tcsetattr(int fd, int optional_actions, const struct termios *termios_p);
int tcsendbreak(int fd, int duration);
int tcdrain(int fd);
int tcflush(int fd, int queue_selector);
int tcflow(int fd, int action);
```

## Capability Translation Layer

### File Descriptor to Capability Mapping

```c
typedef struct fd_cap_map {
    int fd;                    // POSIX file descriptor
    exo_cap capability;        // Exokernel capability
    int flags;                 // O_RDONLY, O_WRONLY, etc.
    off_t offset;             // Current file position
    struct fd_cap_map *next;  // Linked list
} fd_cap_map_t;

// Global FD table (per-process in LibOS space)
static fd_cap_map_t *fd_table[FD_MAX];

int libos_open(const char *path, int flags, mode_t mode) {
    // 1. Request capability from exokernel
    exo_cap cap = exo_request_file_cap(path, flags);
    
    // 2. Allocate FD and map to capability
    int fd = allocate_fd();
    fd_table[fd] = create_mapping(fd, cap, flags);
    
    // 3. Return POSIX FD
    return fd;
}
```

### Process ID to Capability Mapping

```c
typedef struct pid_cap_map {
    pid_t pid;                 // POSIX process ID
    exo_cap proc_cap;         // Process capability
    exo_cap ipc_cap;          // IPC endpoint capability
} pid_cap_map_t;

pid_t libos_fork(void) {
    // 1. Request process creation capability
    exo_cap child_cap = exo_create_process();
    
    // 2. Duplicate current process state
    exo_duplicate_state(child_cap);
    
    // 3. Map to POSIX PID
    pid_t child_pid = allocate_pid();
    register_pid_mapping(child_pid, child_cap);
    
    return child_pid;
}
```

## Resource Policy Implementation

### Memory Allocation Policy

```c
// User-space page allocator using exokernel capabilities
typedef struct page_allocator {
    exo_cap mem_cap;          // Memory capability
    void *base;               // Base address
    size_t size;              // Total size
    bitmap_t *free_pages;     // Free page bitmap
} page_allocator_t;

void *libos_mmap(void *addr, size_t len, int prot, int flags, 
                 int fd, off_t offset) {
    // 1. Request memory capability
    exo_cap mem_cap = exo_request_memory(len);
    
    // 2. Apply protection flags
    exo_set_protection(mem_cap, prot);
    
    // 3. Map to virtual address
    void *va = exo_map_capability(mem_cap, addr);
    
    // 4. If file-backed, bind to file capability
    if (fd >= 0) {
        exo_cap file_cap = fd_to_capability(fd);
        exo_bind_memory_file(mem_cap, file_cap, offset);
    }
    
    return va;
}
```

### Scheduling Policy

```c
// User-space scheduler integration
typedef struct sched_policy {
    int priority;
    int time_slice;
    exo_cap cpu_cap;
} sched_policy_t;

int libos_nice(int inc) {
    // 1. Get current CPU capability
    exo_cap cpu_cap = exo_get_cpu_cap();
    
    // 2. Adjust priority in user-space scheduler
    sched_policy_t *policy = get_current_policy();
    policy->priority += inc;
    
    // 3. Update exokernel scheduling hint
    exo_set_scheduling_hint(cpu_cap, policy->priority);
    
    return 0;
}
```

## Testing Strategy

### 1. Unit Tests (tests/libos/)
- Test each POSIX function individually
- Verify capability translation correctness
- Check error handling and errno setting

### 2. POSIX Compliance Tests (tests/posix_compliance/)
- Run POSIX Test Suite (PTS) when available
- Test against SUSv5 specifications
- Verify signal delivery and threading

### 3. Integration Tests (tests/integration/)
- Test real POSIX applications
- Verify shell scripts work correctly
- Test process groups and sessions

### 4. Performance Tests (tests/performance/)
- Measure syscall overhead vs traditional kernel
- Test IPC performance
- Benchmark file I/O operations

## Implementation Priorities

### Phase 1: Core POSIX (Current Sprint)
1. ✅ Complete errno system
2. ✅ Implement signal handling
3. ✅ Basic file operations
4. ⏳ Process management (fork, exec, wait)
5. ⏳ Basic memory management (mmap, munmap)

### Phase 2: Extended POSIX
1. Time functions
2. User/group management
3. Terminal I/O completion
4. Advanced file operations (chmod, chown)
5. Directory traversal (opendir, readdir)

### Phase 3: Full Compliance
1. Shared memory
2. Message queues
3. Semaphores
4. Advanced signals (sigqueue, sigtimedwait)
5. Process groups and sessions

### Phase 4: Optimization
1. Fast-path for common operations
2. Zero-copy I/O
3. Lazy capability allocation
4. User-space caching

## Exokernel-Specific Extensions

### 1. Direct Hardware Access
```c
// Extension for direct device access
exo_cap libos_request_device(const char *device);
int libos_map_device_memory(exo_cap dev_cap, void **addr);
```

### 2. Custom Schedulers
```c
// Extension for custom scheduling policies
int libos_register_scheduler(exo_cap cpu_cap, 
                             void (*scheduler)(void));
int libos_yield_to(pid_t target_pid);
```

### 3. Zero-Copy IPC
```c
// Extension for high-performance IPC
int libos_share_memory(pid_t target, void *addr, size_t len);
int libos_fast_call(exo_cap endpoint, void *msg);
```

## Migration Guide

### For Existing POSIX Applications

1. **No Source Changes Required**
   - Link against libexoc instead of libc
   - Most POSIX applications work unmodified

2. **Performance Tuning**
   - Use exokernel extensions for critical paths
   - Implement custom resource policies

3. **Known Limitations**
   - Some /proc filesystem features unavailable
   - Limited ptrace support
   - No kernel modules

### For New Applications

1. **Hybrid Approach**
   - Use POSIX API for portability
   - Use exokernel API for performance

2. **Direct Capability Use**
   - Bypass POSIX layer when needed
   - Implement custom resource management

## References

- POSIX.1-2024 (SUSv5) Specification (docs/standards/posix/)
- FeuerBird Exokernel Design (ARCHITECTURE.md)
- Capability Model (docs/CAPABILITY_MODEL.md)
- IPC Design (doc/IPC.md)