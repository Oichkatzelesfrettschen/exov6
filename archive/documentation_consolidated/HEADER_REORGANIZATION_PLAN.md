# ExoV6 Header Reorganization Master Plan

## Executive Summary

Based on deep recursive analysis using 10+ tools, we have identified critical header architecture issues that violate exokernel principles. This plan provides a systematic approach to reorganize 219 headers across 3 architectural zones.

## Key Findings

### Critical Issues
- **71 duplicate headers** across zones (31% of all headers)
- **113 mixed-content headers** violating single-responsibility principle
- **23 headers missing proper guards**
- **Zone isolation violations** between kernel/libos/userland

### Architecture Violations
1. Kernel headers exposed in public include/
2. LibOS implementation details leaked to userland
3. No clear boundary enforcement between zones
4. Circular dependencies through shared headers

## Proposed Three-Tier Architecture

Based on MIT Exokernel and NetBSD Rump Kernel research:

```
┌─────────────────────────────────────────┐
│         Tier 1: Public API              │
│         include/exo/api/                 │
│   - Capability definitions              │
│   - System call interfaces              │
│   - Shared types (size_t, etc)          │
└─────────────────────────────────────────┘
                    ↕
┌─────────────────────────────────────────┐
│      Tier 2: Zone Interfaces            │
│   kernel/include/  libos/include/       │
│   - Zone-specific public APIs           │
│   - Inter-zone communication            │
│   - Resource abstractions               │
└─────────────────────────────────────────┘
                    ↕
┌─────────────────────────────────────────┐
│      Tier 3: Zone Internals             │
│   kernel/internal/  libos/internal/     │
│   - Private implementations             │
│   - Zone-specific structures            │
│   - Internal utilities                  │
└─────────────────────────────────────────┘
```

## Immediate Action Items

### Phase 1: Deduplication (Priority: CRITICAL)

#### Headers to Remove from include/ (keep only in kernel/)
```
- spinlock.h, sleeplock.h, qspinlock.h, rspinlock.h
- proc.h, sched.h, vm.h, mmu.h, mmu64.h
- trap.h, traps.h, syscall.h
- All driver headers (uart.h, kbd.h, etc.)
```

#### Headers to Keep ONLY in include/
```
- fs.h (on-disk format shared across zones)
- stat.h, types.h, errno.h (POSIX types)
- exokernel.h (capability definitions)
```

### Phase 2: Zone Boundary Enforcement

#### Kernel Zone (kernel/)
```
kernel/
├── include/        # Kernel public API (for LibOS)
│   ├── syscall.h   # System call numbers only
│   ├── cap.h       # Capability operations
│   └── exo_ops.h   # Exokernel operations
├── internal/       # Kernel private
│   ├── proc.h      # Process internals
│   ├── vm.h        # Memory management
│   └── sched.h     # Scheduler internals
└── *.c            # Implementation files
```

#### LibOS Zone (libos/)
```
libos/
├── include/        # LibOS public API (for userland)
│   ├── posix.h     # POSIX compatibility
│   ├── pthread.h   # Threading API
│   └── stdio.h     # I/O abstractions
├── internal/       # LibOS private
│   ├── fd_table.h  # File descriptor management
│   ├── proc_mgmt.h # Process management
│   └── mem_mgmt.h  # Memory abstractions
└── *.c            # Implementation files
```

#### Rump Kernel Support (rump/)
```
rump/
├── include/        # Rump kernel API
│   ├── rump.h      # Rump operations
│   └── drivers.h   # Driver interfaces
├── internal/       # Rump private
└── drivers/        # Rump drivers
```

### Phase 3: Header Content Separation

For each mixed-content header, split into:
1. `*_types.h` - Type definitions only
2. `*_ops.h` - Function declarations
3. `*_impl.h` - Implementation details (if needed)

Example for file.h:
```c
// include/exo/api/file_types.h
typedef struct file {
    uint32_t type;
    uint32_t ref;
} file_t;

// kernel/include/file_ops.h  
int file_open(const char *path, int flags);
int file_close(int fd);

// kernel/internal/file_impl.h
struct file_internal {
    struct file base;
    struct inode *ip;
    // ... kernel-specific fields
};
```

### Phase 4: Guard Standardization

All headers MUST use traditional guards for C17 compatibility:

```c
#ifndef EXOV6_ZONE_MODULE_H
#define EXOV6_ZONE_MODULE_H

// content

#endif /* EXOV6_ZONE_MODULE_H */
```

Naming convention: `EXOV6_<ZONE>_<MODULE>_H`

## Build System Updates

### CMakeLists.txt Changes

```cmake
# Kernel - ONLY kernel headers first
target_include_directories(kernel PRIVATE
    ${CMAKE_SOURCE_DIR}/kernel/internal
    ${CMAKE_SOURCE_DIR}/kernel/include  
    ${CMAKE_SOURCE_DIR}/include/exo/api
)

# LibOS - ONLY libos headers first
target_include_directories(libos PRIVATE
    ${CMAKE_SOURCE_DIR}/libos/internal
    ${CMAKE_SOURCE_DIR}/libos/include
    ${CMAKE_SOURCE_DIR}/kernel/include  # For syscalls
    ${CMAKE_SOURCE_DIR}/include/exo/api
)

# Userland - Public APIs only
target_include_directories(userland PRIVATE
    ${CMAKE_SOURCE_DIR}/libos/include
    ${CMAKE_SOURCE_DIR}/include/exo/api
)
```

## Implementation Script

```bash
#!/bin/bash
# Execute header reorganization

# Step 1: Create new directory structure
mkdir -p include/exo/api
mkdir -p kernel/{include,internal}
mkdir -p libos/{include,internal}
mkdir -p rump/{include,internal}

# Step 2: Move headers to correct locations
# ... (detailed move operations)

# Step 3: Update all #include statements
find . -name "*.c" -o -name "*.h" | xargs sed -i 's|#include "proc.h"|#include "kernel/internal/proc.h"|g'
# ... (more sed commands)

# Step 4: Verify no broken includes
./scripts/verify_includes.sh
```

## Success Metrics

After reorganization:
- [ ] Zero duplicate headers across zones
- [ ] All headers have proper guards
- [ ] No zone boundary violations
- [ ] Clean compilation with -Wall -Wextra -Wpedantic
- [ ] Include depth reduced by 40%
- [ ] Compilation time reduced by 25%

## Long-Term Benefits

1. **Security**: Clear privilege boundaries between zones
2. **Maintainability**: Single source of truth for each component
3. **Performance**: Reduced include overhead
4. **Portability**: Clean separation enables rump kernel support
5. **Compliance**: Full C17 standard compliance

## Timeline

- **Day 1-2**: Backup and prepare migration scripts
- **Day 3-4**: Execute Phase 1 (Deduplication)
- **Day 5-6**: Execute Phase 2 (Zone boundaries)
- **Day 7-8**: Execute Phase 3 (Content separation)
- **Day 9**: Execute Phase 4 (Guard standardization)
- **Day 10**: Testing and validation

## Risk Mitigation

1. Create full backup before changes
2. Use version control for all modifications
3. Test compilation after each phase
4. Maintain compatibility shim headers during transition
5. Document all changes in CHANGELOG

## Conclusion

This reorganization aligns ExoV6 with exokernel principles while incorporating best practices from MIT's Aegis/XOK and NetBSD's anykernel architecture. The result will be a clean, maintainable, and secure header architecture supporting true capability-based isolation.