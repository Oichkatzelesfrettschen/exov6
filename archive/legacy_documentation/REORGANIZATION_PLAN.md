# Repository Reorganization Plan

## Executive Summary

This plan addresses the repository's current issues:
- 411 build artifacts cluttering directories
- Stray files in root directory
- 227 user files with many duplicates (_real, _simple, _working variants)
- Mixed naming conventions (.cpp, .cpp23, numbered files)
- Unorganized kernel/libos subsystems
- Duplicate "engine" directory structure

## Current State Analysis

### File Distribution
```
Location          | C Files | Issues
------------------|---------|------------------------------------------
Root              | 20+     | Headers, boot files, tests mixed in root
kernel/           | 78      | Flat structure, no subsystem organization
libos/            | 30      | Flat structure, mixed concerns
user/             | 227     | Many duplicates (17 sets of variants)
engine/           | ~50     | Duplicate structure, needs merging
demos/            | 30      | Good location, keep as-is
```

### Duplicate Files Identified
- **User variants**: cat, echo, pwd, test, sh, ls, wc, true, false (each has 2-4 versions)
- **Headers**: `exo_cpu.h` and `exo_cpu 3.h` (space in filename)
- **Spinlocks**: 5 implementations (spinlock.c, qspinlock.c, rspinlock.c, modern_locks.c, rcu.c)
- **Boot files**: Multiple versions in root

## Proposed Structure

```
feuerbird_exokernel/
├── kernel/                  # Ring 0 exokernel
│   ├── boot/               # Boot and initialization
│   │   ├── bootasm.S
│   │   ├── bootmain.c
│   │   └── entry.S
│   ├── drivers/            # Device drivers
│   │   ├── console.c
│   │   ├── kbd.c
│   │   ├── uart.c
│   │   └── ide.c
│   ├── fs/                 # File system
│   │   ├── fs.c
│   │   ├── bio.c
│   │   └── log.c
│   ├── ipc/                # Inter-process communication
│   │   ├── exo_ipc.c
│   │   ├── fastipc.c
│   │   ├── endpoint.c
│   │   └── cap.c
│   ├── mem/                # Memory management
│   │   ├── vm.c
│   │   ├── kalloc.c
│   │   └── mmu64.c
│   ├── sched/              # Scheduling
│   │   ├── proc.c
│   │   ├── sched.c
│   │   └── beatty_sched.c
│   ├── sync/               # Synchronization
│   │   ├── spinlock.c     # Unified implementation
│   │   ├── sleeplock.c
│   │   └── rcu.c
│   └── sys/                # System calls and traps
│       ├── syscall.c
│       ├── trap.c
│       └── vectors.S
│
├── libos/                   # User-space OS library
│   ├── posix/              # POSIX API layer
│   │   └── posix.c
│   ├── pthread/            # Threading
│   │   ├── pthread_core.c
│   │   └── pthread_mutex.c
│   ├── signal/             # Signal handling
│   │   └── signal_posix.c
│   ├── fs/                 # File operations
│   │   └── fs.c
│   └── mem/                # Memory operations
│       └── memory.c
│
├── user/                    # User programs
│   ├── bin/                # Core utilities (deduplicated)
│   │   ├── cat.c
│   │   ├── echo.c
│   │   ├── ls.c
│   │   └── ...
│   ├── sbin/               # System utilities
│   │   ├── init.c
│   │   └── mount.c
│   ├── shell/              # Shell implementation
│   │   └── sh.c
│   └── variants_backup/    # Archived duplicates
│
├── include/                 # Header files
│   ├── kernel/             # Kernel headers
│   ├── libos/              # LibOS headers
│   └── sys/                # System headers
│
├── tools/                   # Build and development tools
│   ├── mkfs.c
│   └── build/
│
├── tests/                   # Test suites
│   ├── unit/               # Unit tests
│   ├── integration/        # Integration tests
│   └── posix/              # POSIX compliance tests
│
├── demos/                   # Example programs (keep as-is)
├── docs/                    # Documentation (keep as-is)
└── scripts/                 # Utility scripts (keep as-is)
```

## Reorganization Actions

### Phase 1: Clean Build Artifacts
```bash
# Remove all .o, .d, .asm files
find . -type f \( -name "*.o" -o -name "*.d" -o -name "*.asm" \) -delete

# Clean temporary files
rm -f *.tmp *.bak *~
```

### Phase 2: Deduplicate User Programs
For each utility with variants:
1. Compare line counts and functionality
2. Keep most complete implementation
3. Archive others to `user/variants_backup/`

Example for `cat`:
- Keep `cat_working.c` (most complete)
- Rename to `cat.c`
- Move others to backup

### Phase 3: Organize Root Directory
```bash
# Move headers to include/
mv *.h include/

# Move boot files to kernel/boot/
mv boot*.S bootasm*.S entry*.S kernel/boot/

# Move tools
mv mkfs*.c tools/
```

### Phase 4: Reorganize Kernel by Subsystem
Move files from flat `kernel/` to appropriate subdirectories based on functionality.

### Phase 5: Merge Engine Directory
- Merge `engine/kernel/` with `kernel/`
- Merge `engine/user/` with `user/`
- Handle conflicts by renaming

### Phase 6: Standardize Naming
- Remove `.cpp` and `.cpp23` extensions → `.c`
- Remove numbers from filenames
- Remove `_INFO` suffixes
- Follow Unix naming conventions

### Phase 7: Consolidate Spinlocks
Create unified `kernel/sync/spinlock.c` that includes:
- Best features from all 5 implementations
- Configurable via compile flags
- Archive old implementations

## Build System Updates

### CMakeLists.txt Changes
- Update all source paths to new structure
- Group sources by subsystem
- Add proper include directories
- Create installation targets

### Makefile Updates
- Update OBJS paths
- Add subdirectory rules
- Update dependency generation

## Migration Script

A comprehensive script `scripts/reorganize_repository.sh` will:
1. Create backup
2. Execute all phases
3. Update build files
4. Generate report
5. Test build

## Testing Plan

After reorganization:
```bash
# Clean build test
mkdir build && cd build
cmake .. && make

# Run tests
ctest -V

# QEMU test
make qemu

# Check for missing files
git status
```

## Risk Mitigation

1. **Full Backup**: tar.gz of entire repository before changes
2. **Git Branch**: Work in separate branch
3. **Incremental**: Can be done in phases
4. **Reversible**: Script tracks all moves

## Expected Outcomes

- **Cleaner Structure**: Logical organization by subsystem
- **Reduced Files**: ~23% reduction from deduplication
- **Better Navigation**: Clear directory purposes
- **Easier Maintenance**: Standard Unix layout
- **Faster Builds**: No redundant compilations

## Implementation Timeline

1. **Immediate** (5 min): Run reorganization script
2. **Test** (10 min): Verify build works
3. **Commit** (2 min): Git commit with detailed message
4. **Document** (5 min): Update README and CLAUDE.md

Total time: ~22 minutes

## Command to Execute

```bash
# Make script executable
chmod +x scripts/reorganize_repository.sh

# Run reorganization
./scripts/reorganize_repository.sh

# Verify changes
git status
git diff --stat

# Test build
mkdir build && cd build
cmake .. && make -j$(nproc)

# If successful, commit
git add -A
git commit -m "Reorganize repository structure: deduplicate files, organize by subsystem, standardize naming"
```