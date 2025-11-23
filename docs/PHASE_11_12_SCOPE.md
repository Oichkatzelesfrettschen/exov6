# Phase 11-12 Scope: Shell and Multi-Application Society

## Research Summary

### Sources Consulted
- [MIT Exokernel (ExOS)](https://pdos.csail.mit.edu/archive/exo/) - spawn vs fork/exec
- [seL4 Microkernel](https://sel4.systems/) - capability-based process management
- [MIT 6.828 Lab 5: Spawn and Shell](https://pdos.csail.mit.edu/6.828/2012/labs/lab5/)
- [xv6 Shell Implementation](https://pdos.csail.mit.edu/6.828/2019/labs/sh.html)
- [POSIX spawn performance](https://blog.famzah.net/2018/12/19/posix_spawn-performance-benchmarks-and-usage-examples/)
- [Microkernel IPC patterns](https://en.wikipedia.org/wiki/Microkernel)

### Key Design Decisions

#### 1. spawn() instead of fork()+exec()
> "We implemented spawn rather than a UNIX-style exec because spawn is easier
> to implement from user space in 'exokernel fashion', without special help
> from the kernel." - MIT 6.828

In exokernel design, the child cannot easily modify its own address space
while running inside it. Instead, the **parent** handles everything:
1. Create blank environment (sys_env_create)
2. Load ELF segments into child's address space
3. Set up file descriptors
4. Start execution (sys_env_run)

#### 2. File Descriptors via LibOS
File descriptors are a **LibOS abstraction**, not a kernel concept:
- LibOS maintains per-process FD table
- FDs map to: fs_srv handles, pipe endpoints, device handles
- On spawn(), parent copies FD table to child via shared memory

#### 3. Pipes via IPC
Pipes are implemented entirely in user space:
- Pipe server maintains ring buffers
- Read/write via IPC messages
- EOF when all write ends closed

#### 4. Shell Parser (xv6 style)
Recursive descent parser with command types:
- EXEC: Simple command with arguments
- REDIR: Command with < or > redirection
- PIPE: Two commands connected by |

---

## Phase 11: The Shell ("The Voice")

### 11.1 spawn() Implementation
**Goal**: Create child processes from ELF files

```
spawn(path, argv, envp) -> pid
  1. Open ELF file via fs_srv
  2. sys_env_create() - blank child
  3. Load ELF into child (lib/elf/)
  4. Copy FD table to child
  5. Set up argv/envp on child stack
  6. sys_env_run() - start child
  7. Return child PID
```

### 11.2 File Descriptor Layer
**Goal**: POSIX-like FD abstraction in LibOS

```c
struct file_desc {
    int type;           // FD_NONE, FD_FILE, FD_PIPE, FD_DEV
    int server_handle;  // Handle from fs_srv or pipe_srv
    int flags;          // O_RDONLY, O_WRONLY, etc.
    int ref_count;      // For dup()
};

// Per-process FD table
struct file_desc fd_table[MAX_FDS];
```

Operations:
- `fd_open(path, flags)` - Open via fs_srv, allocate FD
- `fd_close(fd)` - Close handle, free FD
- `fd_read(fd, buf, n)` - Read via appropriate server
- `fd_write(fd, buf, n)` - Write via appropriate server
- `fd_dup(fd)` - Duplicate FD (same handle, ref++)
- `fd_dup2(old, new)` - Duplicate to specific number

### 11.3 Pipe Implementation
**Goal**: Inter-process communication via pipes

Design options:
1. **Kernel pipe buffer** - Add SYS_pipe syscall (simpler)
2. **User-space pipe server** - Pure exokernel (consistent)

We'll use option 2 for purity:
```
pipe() -> (read_fd, write_fd)
  1. Allocate pipe ID
  2. Create read endpoint FD
  3. Create write endpoint FD
  4. Register with pipe_server
```

### 11.4 Shell Parser
**Goal**: Parse commands like xv6 shell

Command types:
```c
#define EXEC  1   // Simple command
#define REDIR 2   // Redirection
#define PIPE  3   // Pipeline

struct execcmd { char *argv[MAXARGS]; };
struct redircmd { struct cmd *cmd; char *file; int mode; int fd; };
struct pipecmd { struct cmd *left; struct cmd *right; };
```

Parser functions:
- `parsecmd()` - Entry point
- `parseline()` - Parse full line
- `parsepipe()` - Handle |
- `parseredirs()` - Handle < >
- `parseexec()` - Parse simple command
- `parseblock()` - Handle ( ) grouping

### 11.5 Command Execution
**Goal**: Execute parsed commands

```c
void runcmd(struct cmd *cmd) {
    switch (cmd->type) {
    case EXEC:
        spawn(ecmd->argv[0], ecmd->argv, environ);
        wait();
        break;
    case REDIR:
        // Manipulate FDs before spawn
        if (rcmd->mode == O_RDONLY)
            fd_dup2(fd_open(rcmd->file, O_RDONLY), 0);
        else
            fd_dup2(fd_open(rcmd->file, O_WRONLY|O_CREAT), 1);
        runcmd(rcmd->cmd);
        break;
    case PIPE:
        pipe(p);
        if ((pid = spawn(...)) == 0) {  // Left side
            fd_dup2(p[1], 1);  // stdout -> pipe write
            fd_close(p[0]);
            runcmd(pcmd->left);
        }
        // Right side
        fd_dup2(p[0], 0);  // stdin -> pipe read
        fd_close(p[1]);
        runcmd(pcmd->right);
        wait();
        break;
    }
}
```

### 11.6 Process Wait
Already have: `sys_wait()` in kernel
Need: LibOS wrapper that handles our spawn model

### 11.7 Basic Utilities
Essential for shell testing:
- `cat` - Concatenate files
- `echo` - Print arguments
- `ls` - List directory (via fs_srv)
- `wc` - Word count
- `grep` - Pattern matching (simple)

---

## Phase 12: Multi-Application Society

### 12.1 Service Registry
**Goal**: Named service discovery

```c
// Register a service
service_register("fs", getpid());

// Look up a service
int fs_pid = service_lookup("fs");
```

Implementation: Simple IPC to init process which maintains registry.

### 12.2 Device Manager
**Goal**: User-space device enumeration

```c
// Query available devices
device_list(devs, &count);

// Claim a device (get capability)
int cap = device_claim("virtio-blk0");
```

### 12.3 Network Stack (Optional)
**Goal**: User-space TCP/IP

Following exokernel model:
- Raw packet access via capability
- TCP/IP implemented in LibOS
- Socket abstraction in LibOS

### 12.4 Multi-User Support (Optional)
**Goal**: Basic user isolation

- UID/GID in process structure
- File permission checking in fs_srv
- Login/authentication service

---

## Implementation Order

### Week 1: Core spawn()
1. 11.1.1 spawn.h interface
2. 11.1.2 spawn() implementation
3. 11.6.1 wait() wrapper
4. 11.7.2 echo utility (test spawn)

### Week 2: File Descriptors
1. 11.2.1 fd_table structure
2. 11.2.2 fd_open/close/read/write
3. 11.2.3 fd_dup/dup2
4. 11.7.1 cat utility (test FDs)

### Week 3: Shell
1. 11.4.1 shell main loop
2. 11.4.2-11.4.3 parser (exec)
3. 11.4.4 parser (redir)
4. 11.5.1-11.5.2 runcmd (exec, redir)

### Week 4: Pipes
1. 11.3.1 sys_pipe or pipe_server
2. 11.4.5 parser (pipe)
3. 11.5.3 runcmd (pipe)
4. 11.7.3-11.7.5 ls, wc, grep

### Week 5: Integration
1. 11.8.1-11.8.3 End-to-end tests
2. Bug fixes and polish
3. Documentation

---

## Success Criteria

Phase 11 is complete when:
```
$ echo hello world
hello world
$ cat < README.md
(file contents)
$ ls | grep .c
init.c
hello.c
...
$ echo hello | cat | wc
      1       1       6
```

Phase 12 is complete when:
- Multiple services can register and be discovered
- At least one additional service (device manager) works
- System boots to shell automatically
