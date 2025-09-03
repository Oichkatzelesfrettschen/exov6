# FeuerBird C++23 Migration & Restructuring Tracker

## Overview
This document tracks the progress of migrating FeuerBird from C17 to C++23, restructuring by license, and eliminating code duplication.

## Migration Phases

### Phase 0: Preparation [IN PROGRESS]
- [x] Create CLAUDE.md with comprehensive guidance
- [x] Create restructuring scripts
- [x] Create deduplication scripts
- [x] Create libc++ bootstrap script
- [ ] Backup current codebase
- [ ] Set up CI/CD for C++23
- [ ] Create migration branches

### Phase 1: Infrastructure (Week 1)
#### Day 1-2: LLVM libc++ Setup
- [ ] Run `scripts/bootstrap_libcxx.sh`
- [ ] Verify C++23 compilation
- [ ] Test std::expected, std::span, concepts
- [ ] Create kernel allocator adapters

#### Day 3-4: Directory Restructuring
- [ ] Run `scripts/restructure_by_license.sh`
- [ ] Move BSD code to `bsd/`
- [ ] Move GPL code to `gpl/`
- [ ] Move MIT code to `mit/`
- [ ] Set up Limine in `limine/`

#### Day 5-7: Build System Updates
- [ ] Update Makefile for C++23
- [ ] Update meson.build for new structure
- [ ] Create per-directory build configs
- [ ] Test incremental builds

### Phase 2: Kernel Migration (Week 2)
#### Core Kernel (Days 1-3)
- [ ] Convert `kernel/main.c` → `main.cpp`
- [ ] Convert capability system to C++ classes
- [ ] Migrate memory management
- [ ] Update trap/interrupt handlers

#### Synchronization (Days 4-5)
- [ ] Unify spinlock implementations
  - [ ] Remove qspinlock.c, rspinlock.c duplicates
  - [ ] Create single `spinlock.hpp` with templates
- [ ] Convert RCU to C++23
- [ ] Update atomic operations

#### IPC System (Days 6-7)
- [ ] Convert IPC to std::expected
- [ ] Implement typed channels with concepts
- [ ] Update capability validation
- [ ] Test zone boundaries

### Phase 3: LibOS Migration (Week 3)
#### POSIX Layer (Days 1-3)
- [ ] Convert `libos/posix.c` → `posix.cpp`
- [ ] Replace errno with std::expected
- [ ] Implement thread-local storage
- [ ] Update signal handling

#### File System (Days 4-5)
- [ ] Convert FS layer to C++23
- [ ] Use std::span for buffers
- [ ] Implement path utilities
- [ ] Update VFS abstractions

#### Threading (Days 6-7)
- [ ] Convert pthread implementation
- [ ] Use std::jthread where applicable
- [ ] Update synchronization primitives
- [ ] Test POSIX compliance

### Phase 4: User Space (Week 4)
#### Utility Deduplication (Days 1-2)
- [ ] Run `scripts/deduplicate_utilities.sh`
- [ ] Merge cat variants → single cat.cpp
- [ ] Merge echo variants → single echo.cpp
- [ ] Merge pwd variants → single pwd.cpp
- [ ] Merge test variants → single test.cpp
- [ ] Merge shell variants → single sh.cpp

#### Utility Migration (Days 3-5)
- [ ] Convert all utilities to C++23
- [ ] Use std::format for output
- [ ] Use std::string_view for arguments
- [ ] Implement option parsing templates

#### Testing & Validation (Days 6-7)
- [ ] Run POSIX compliance tests
- [ ] Run performance benchmarks
- [ ] Fix regressions
- [ ] Update documentation

## Code Statistics

### Current State (C17)
| Component | Files | Lines | Duplicates |
|-----------|-------|-------|------------|
| Kernel    | 79    | ~15K  | 5 spinlocks |
| LibOS     | 34    | ~8K   | -          |
| User      | 228   | ~25K  | 17 variants |
| Total     | 341   | ~48K  | 22         |

### Target State (C++23)
| Component | Files | Lines | Reduction |
|-----------|-------|-------|-----------|
| Kernel    | ~60   | ~12K  | 20%       |
| LibOS     | ~30   | ~7K   | 12%       |
| User      | ~150  | ~18K  | 28%       |
| Total     | ~240  | ~37K  | 23%       |

## File Migration Status

### Kernel Files (Priority)
- [ ] main.c → main.cpp
- [ ] proc.c → process.cpp
- [ ] vm.c → memory.cpp
- [ ] trap.c → trap.cpp
- [ ] syscall.c → syscall.cpp
- [ ] fs.c → filesystem.cpp
- [ ] spinlock.c → synchronization.hpp
- [ ] cap.c → capability.cpp
- [ ] exo_ipc.c → ipc.cpp

### LibOS Files
- [ ] posix.c → posix.cpp
- [ ] pthread_core.c → threading.cpp
- [ ] signal_posix.c → signals.cpp
- [ ] fs_ext.c → fs_extensions.cpp
- [ ] memory.c → memory_mgmt.cpp

### Duplicate Consolidation
- [ ] cat_real.c + cat_simple.c + cat_working.c → cat.cpp
- [ ] echo_real.c + echo_simple.c + echo_working.c → echo.cpp
- [ ] pwd_real.c + pwd_simple.c + pwd_working.c → pwd.cpp
- [ ] test_real.c + test_simple.c + test_working.c → test.cpp
- [ ] sh.c + sh_working.c → sh.cpp
- [ ] true.c + true_real.c → true.cpp
- [ ] false.c + false_real.c → false.cpp
- [ ] wc.c + wc_real.c → wc.cpp
- [ ] ls.c + ls_simple.c → ls.cpp

## Testing Checkpoints

### Checkpoint 1: Infrastructure
- [ ] libc++ builds successfully
- [ ] Test program compiles with C++23
- [ ] Directory structure reorganized
- [ ] Build system updated

### Checkpoint 2: Kernel
- [ ] Kernel boots with C++23
- [ ] Capabilities work
- [ ] IPC functional
- [ ] Spinlocks unified

### Checkpoint 3: LibOS
- [ ] POSIX layer functional
- [ ] File operations work
- [ ] Threading operational
- [ ] Signals handled

### Checkpoint 4: User Space
- [ ] All utilities deduplicated
- [ ] Shell works
- [ ] Pipelines functional
- [ ] POSIX tests pass

## Risk Mitigation

### High Risk Areas
1. **Interrupt Handlers**: Must remain C-compatible
   - Solution: Use extern "C" wrappers
   
2. **Assembly Interface**: Cannot use C++ features
   - Solution: Maintain C interface layer
   
3. **Boot Code**: Must be freestanding
   - Solution: Minimal C++ runtime

4. **Driver Compatibility**: GPL boundary
   - Solution: C interface for drivers

### Rollback Plan
1. All changes in separate branch
2. Original C17 code backed up
3. Incremental migration allows partial rollback
4. Each phase independently testable

## Performance Targets

### Must Maintain
- Boot time: < 1 second
- Context switch: < 2000 cycles
- IPC latency: < 1000 cycles
- Memory allocation: O(1)

### Expected Improvements
- Binary size: -20% (no exceptions/RTTI)
- Compile time: -30% (modules)
- Type safety: +100% (concepts)
- Error handling: Cleaner with std::expected

## Success Criteria

### Phase 1 Complete When:
- [x] Scripts created and tested
- [ ] libc++ built with C++23
- [ ] Directory structure reorganized
- [ ] Build systems updated

### Phase 2 Complete When:
- [ ] Kernel compiles as C++23
- [ ] Kernel boots successfully
- [ ] All kernel tests pass
- [ ] Performance targets met

### Phase 3 Complete When:
- [ ] LibOS fully migrated
- [ ] POSIX compliance maintained
- [ ] Threading works correctly
- [ ] File operations functional

### Phase 4 Complete When:
- [ ] All duplicates eliminated
- [ ] All utilities migrated
- [ ] POSIX test suite passes
- [ ] Documentation updated

## Notes & Issues

### Known Blockers
- None identified yet

### Dependencies
- LLVM/Clang 18+ for full C++23
- CMake 3.28+ for module support
- Ninja for fast builds

### Decisions Needed
- [ ] Module partition strategy
- [ ] Coroutine usage in kernel?
- [ ] std::pmr allocator usage?

## Weekly Reports

### Week 0 (Preparation)
- Created comprehensive documentation
- Developed migration scripts
- Analyzed codebase structure
- Identified 22 duplicate implementations

### Week 1 (Planned)
- TBD

### Week 2 (Planned)
- TBD

### Week 3 (Planned)
- TBD

### Week 4 (Planned)
- TBD