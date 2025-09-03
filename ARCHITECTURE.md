# FeuerBird Exokernel Architecture

## Overview

FeuerBird is a POSIX-2024 (SUSv5) compliant exokernel operating system that separates mechanism from policy, providing minimal kernel abstractions while delegating OS services to user-space Library Operating Systems (LibOS). Originally based on Unix v6, it has been enhanced with modern exokernel capabilities including capability-based IPC, typed channels, and user-space drivers.

## Core Design Principles

### 1. Exokernel Philosophy
- **Minimal Abstraction**: Kernel provides raw hardware access, not high-level abstractions
- **Secure Multiplexing**: Safe sharing of hardware resources among applications
- **Application Control**: Applications have maximum control over resource management
- **LibOS Flexibility**: Multiple LibOS implementations can coexist

### 2. Three-Zone Architecture

```
┌─────────────────────────────────────────┐
│         Application Zone                 │
│         (Ring 3, User)                   │
│    - User applications                   │
│    - Custom resource policies             │
└─────────────────────────────────────────┘
                    ↕ Capabilities
┌─────────────────────────────────────────┐
│           LibOS Zone                     │
│         (Ring 3, Privileged)             │
│    - POSIX implementation                │
│    - System call emulation               │
│    - Resource management                 │
└─────────────────────────────────────────┘
                    ↕ Secure Bindings
┌─────────────────────────────────────────┐
│          Kernel Zone                     │
│         (Ring 0, Kernel)                 │
│    - Hardware multiplexing               │
│    - Capability enforcement              │
│    - Zone isolation                      │
└─────────────────────────────────────────┘
```

## Capability-Based Security

### Capability System Components

1. **Capability Table** (`kernel/cap_table.c`)
   - 65536 capability slots
   - Per-boot secret with MAC-based authentication (HMAC-SHA256; stubbed today)
   - Atomic reference counting
   - Thread-safe operations

2. **Capability Types**
   ```c
   typedef enum {
       CAP_TYPE_MEMORY,     // Physical memory access
       CAP_TYPE_CPU,        // CPU time allocation
       CAP_TYPE_DISK,       // Disk block access
       CAP_TYPE_NET,        // Network interface
       CAP_TYPE_IPC,        // Inter-process communication
       CAP_TYPE_ZONE        // Zone transition
   } cap_type_t;
   ```

3. **Authentication Flow**
   ```
   Request → Validate Hash → Check Permissions → Grant Access
   ```

### Secure Bindings

Secure bindings connect LibOS abstractions to kernel resources:

```c
struct secure_binding {
    cap_id_t capability;      // Kernel capability
    void *resource;           // Hardware resource
    uint32_t permissions;     // Access rights
    zone_id_t owner_zone;     // Owning zone
};
```

## Zone Isolation Mechanisms

### Zone Boundaries

1. **Memory Isolation**
   - Page table separation
   - No shared memory by default
   - Explicit capability-based sharing

2. **Execution Isolation**
   - Separate code segments
   - Control flow integrity
   - Zone-specific entry points

3. **Data Isolation**
   - Zone-local heap allocation
   - Capability-protected cross-zone mapping
   - Secure IPC channels

### Zone Transition Protocol

```c
// Zone transition requires:
1. Valid capability
2. Permission check
3. State save/restore
4. Audit logging

zone_transition(ZONE_APP, ZONE_LIBOS, cap, &context);
```

## LibOS Architecture

### POSIX LibOS Implementation

```
User Application
      ↓
POSIX API Layer (libos/)
      ↓
Exokernel Translation
      ↓
Capability Invocation
      ↓
Kernel Services
```

### Key LibOS Components

1. **Process Management** (`libos/process.c`)
   - Fork emulation using exokernel primitives
   - Process table management
   - Signal delivery

2. **Memory Management** (`libos/memory.c`)
   - Virtual memory abstraction
   - Heap management
   - mmap implementation

3. **File System** (`libos/fs.c`)
   - VFS layer
   - File descriptor table
   - Buffer cache

4. **Threading** (`libos/pthread_*.c`)
   - POSIX threads on exokernel threads
   - Synchronization primitives
   - Thread-local storage

## Resource Management

### Physical Memory

```c
// Direct physical page allocation
phys_page_t *page = exo_alloc_page(CAP_MEMORY);

// LibOS virtual memory mapping
void *vaddr = libos_map_page(page, PROT_READ | PROT_WRITE);
```

### CPU Scheduling

```c
// Quantum-based scheduling
struct cpu_quantum {
    uint64_t cycles;
    uint32_t priority;
    cap_id_t cpu_cap;
};
```

### Disk Access

```c
// Direct block access
exo_disk_read(cap, block_num, buffer);

// LibOS file system layer
int fd = open("/path/file", O_RDONLY);
```

## Inter-Process Communication

### Fast IPC Path

```c
// Zero-copy message passing
fastipc_send(&msg);  // kernel/fastipc.c
```

### Shared Memory IPC

```c
// Capability-protected sharing
void *shared = zone_map(from, to, addr, size, cap);
```

## Security Model

### Defense in Depth

1. **Capability Authentication**
   - MAC validation (HMAC-SHA256; upgrading from earlier placeholders)
   - Unforgeable references (per-boot secret)
   - Fine-grained permissions

2. **Zone Isolation**
   - Hardware-enforced boundaries
   - Mandatory access control
   - Audit logging

3. **Secure Bindings**
   - Authenticated resource access
   - Revocable permissions
   - Time-bounded access

### Threat Model

Protected Against:
- Unauthorized resource access
- Zone boundary violations
- Capability forgery
- Privilege escalation

Not Protected Against:
- Hardware attacks
- Side-channel attacks
- Denial of service (partial)

## Performance Optimizations

### Fast Paths

1. **System Call Batching**
   ```c
   exo_batch_syscall(ops, count);
   ```

2. **Direct Hardware Access**
   ```c
   // Bypass LibOS for performance
   exo_direct_io(cap, port, value);
   ```

3. **Zero-Copy Operations**
   ```c
   // Shared memory without copying
   exo_share_pages(cap, pages, count);
   ```

### Scalability

- Per-CPU capability caches
- Lock-free data structures
- NUMA-aware allocation

## Implementation Status

### Completed
- ✅ Core exokernel mechanisms
- ✅ Basic capability system (65536 slots with HMAC authentication)
- ✅ Zone isolation framework (three-zone model)
- ✅ POSIX errno system (133 error codes with thread-local storage)
- ✅ POSIX signal handling (31+ signals with sigaction/sigprocmask)
- ✅ pthread support (create, join, mutex, cond, thread-specific data)
- ✅ Fast IPC with typed channels (Cap'n Proto support)
- ✅ Pluggable schedulers (DAG, Beatty)
- ✅ Basic POSIX utilities (17 commands: cat, ls, cp, mv, pwd, test, etc.)

### In Progress
- 🔄 Full POSIX-2024 (SUSv5) compliance
- 🔄 Extended POSIX utilities (150+ commands required)
- 🔄 Complete libos implementation (mmap, time functions, user/group)
- 🔄 Network stack with capability-based access
- 🔄 Advanced file systems (ext4, ZFS compatibility layers)

### Planned
- ⏳ Quantum-resistant cryptography for capabilities
- ⏳ Distributed capabilities across nodes
- ⏳ Hardware virtualization support
- ⏳ GPU compute capabilities
- ⏳ Persistent capability storage

## Building and Testing

### Build System
```bash
# Recommended: Meson
meson setup build
meson compile -C build

# Alternative: Ninja (via Meson)
meson compile -C build

# Traditional: Make
make
```

### Testing Strategy
- Unit tests for kernel primitives
- Integration tests for LibOS
- Capability verification tests
- Zone isolation tests

## Contributing

See CONTRIBUTING.md for:
- Coding standards (C17, POSIX-2024)
- Architecture guidelines
- Security requirements
- Testing requirements
