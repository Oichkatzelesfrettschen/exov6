# FeuerBird Exokernel - Phase 4 Plan: Build Quality & Core Integration

## Executive Summary

Phase 3 completed lambda_cap integration, formal verification, and Conan setup. Phase 4 focuses on:
1. **Testing Infrastructure Hardening** - Make tests actually block builds
2. **Core Kernel Integration** - Enable excluded high-value files
3. **Documentation Completion** - Fill critical gaps
4. **Quality Gates** - Enforce coverage and performance baselines

---

## Phase 3-4A Completion Status

### ✅ Phase 3 Completed
- Lambda capability engine integrated (20 functions, 173KB kernel)
- Formal verification (4 Rocq proofs: ExoCap, LambdaCap, IRQProof, StreamsProof)
- Capability table (cap.c, cap_table.c) with SipHash authentication
- Experimental code archived (quantum_ipc, genetic_lock, unified_ipc, zero_copy)
- Conan 2 configured (conanfile.py + 3 profiles)
- QEMU boot documented (requires GRUB2 ISO)

### ✅ Phase 4A Completed (Testing Infrastructure)
- Test failures now block CI (removed `|| true` from pytest and ctest)
- Kernel binary validation (ELF format, symbols, multiboot2 header)
- Early serial output added to main64.c with boot_success_marker()
- Coverage infrastructure added (LLVM coverage with 30% threshold)
- New symbols verified: boot_success_marker, main64, early_serial_puts

### 🔄 In Progress
- Architecture harmonization (most experimental variants archived)
- Build system cleanup (gitignore updated, orphaned Makefiles remain)

### ❌ Phase 4B-4D Not Started
- Core kernel file integration (stubs.c, endpoint.c, zone_isolation.c)
- Warning resolution (100+ GNU extension, 31 C23 attribute warnings)
- Documentation (lambda_cap guide, Conan usage, testing strategy)
- Performance baselines

---

## Phase 4 Objectives

### Primary Goals
1. **Harden CI Pipeline**: Tests must pass to merge
2. **Integrate Critical Kernel Files**: VFS (stubs.c), IPC (endpoint.c), Memory (zone_isolation.c)
3. **Document Recent Work**: Lambda_cap guide, Conan usage, testing strategy
4. **Establish Quality Baselines**: Coverage thresholds, performance metrics

### Success Criteria
- CI fails on test failures (no `|| true`)
- Kernel boots in QEMU with validated success marker
- 3+ excluded files re-enabled (stubs.c, endpoint.c, zone_isolation.c)
- Code coverage measured and ≥40%
- Lambda_cap and Conan documented

---

## Implementation Phases

### PHASE 4A: Testing Infrastructure Hardening ✅ COMPLETE

**WHY**: Tests exist but failures are silently ignored. This masks regressions.

**WHAT**: Make test failures block builds, add kernel boot validation, enable coverage

**STATUS**: All tasks completed successfully

#### Task 1: Remove Test Failure Ignoring
**Files**: `.github/workflows/feuerbird_ci.yml`

**Changes**:
```yaml
# BEFORE (Line ~85):
- name: Run Python tests
  run: pytest -v tests/ || true

# AFTER:
- name: Run Python tests
  run: pytest -v tests/ --tb=short

# BEFORE (Line ~90):
- name: Run CMake tests
  run: ctest --output-on-failure || true

# AFTER:
- name: Run CMake tests
  run: ctest --output-on-failure --repeat until-pass:2
```

**Verification**: Intentionally break a test, verify CI fails

#### Task 2: Kernel Boot Validation
**Files**:
- `kernel/boot/main64.c` (add success marker)
- `.github/workflows/feuerbird_ci.yml` (check for marker)

**Implementation**:
```c
// In main64.c after kernel initialization:
void boot_success_marker(void) {
    cprintf("\n=== KERNEL_BOOT_SUCCESS ===\n");
}
```

```yaml
# In CI workflow:
- name: QEMU Boot Test
  run: |
    timeout 30s qemu-system-x86_64 -kernel build/kernel/kernel -nographic -no-reboot > qemu.log 2>&1 || true
    if grep -q "KERNEL_BOOT_SUCCESS" qemu.log; then
      echo "✓ Kernel boot successful"
      exit 0
    else
      echo "✗ Kernel boot failed"
      cat qemu.log
      exit 1
    fi
```

**Verification**: Boot should fail if marker missing

#### Task 3: Enable Code Coverage
**Files**: `.github/workflows/feuerbird_ci.yml`

**Add matrix entry**:
```yaml
- name: Coverage
  build_type: Debug
  cmake_args: "-DENABLE_COVERAGE=ON -DUSE_SIMD=ON"
  sanitizer: ""
```

**Add coverage steps**:
```yaml
- name: Generate Coverage
  if: matrix.name == 'Coverage'
  run: |
    ninja -C build coverage-llvm

- name: Upload Coverage
  if: matrix.name == 'Coverage'
  uses: codecov/codecov-action@v3
  with:
    files: ./build/coverage.info
    fail_ci_if_error: true

- name: Check Coverage Threshold
  if: matrix.name == 'Coverage'
  run: |
    COVERAGE=$(llvm-cov report build/kernel/kernel -instr-profile=build/default.profdata | grep TOTAL | awk '{print $NF}' | sed 's/%//')
    if (( $(echo "$COVERAGE < 40" | bc -l) )); then
      echo "Coverage $COVERAGE% is below 40% threshold"
      exit 1
    fi
```

**Verification**: Check coverage report generated, threshold enforced

---

### PHASE 4B-PRE: Warning Resolution (CRITICAL BLOCKER - 1-2 days)

**WHY**: Build fails with -Werror due to 100+ warnings. Must fix before clean builds.

**WHAT**: Resolve GNU extension and C23 attribute warnings blocking compilation

#### Task 4-Pre: Fix GNU Extension Warnings (BLOCKER)
**Count**: 100+ instances across all compilation units
**Type**: `-Wgnu-include-next`
**Files affected**: include/stdint.h, include/stddef.h, include/sched.h, kernel/stdint.h, kernel/stddef.h

**Root cause**: Headers use `#include_next` to delegate to system headers

**Solution Option 1 (QUICK)**: Add compile flag workaround
```cmake
# In CMakeLists.txt or cmake/CompilerWarnings.cmake:
add_compile_options(-Wno-gnu-include-next)
```

**Solution Option 2 (PROPER)**: Refactor header strategy
- Replace `#include_next` with explicit paths
- Use wrapper headers that don't require GNU extension
- More work but cleaner long-term

**Recommended**: Option 1 initially, Option 2 for Phase 5

#### Task 5-Pre: Fix C23 Attribute Warnings
**Count**: 31 instances across 8 files
**Type**: `-Wc23-extensions`
**Files affected**: compiler_attrs.h (3), cap_security.h (3), defs.h (3), lattice_ipc.h (7), driver.h (12), boundary_check.h (3), exo.h (1), user.h (1)

**Root cause**: Using `[[nodiscard]]`, `[[maybe_unused]]`, `[[noreturn]]` attributes

**Solution Option 1**: Add compile flag
```cmake
add_compile_options(-Wno-c23-extensions)
```

**Solution Option 2**: Force `__attribute__` fallback
```c
// In include/compiler_attrs.h, modify:
#if __has_c_attribute(nodiscard) && !defined(FORCE_GNU_ATTRIBUTES)
  #define EXO_NODISCARD [[nodiscard]]
#else
  #define EXO_NODISCARD __attribute__((warn_unused_result))
#endif
```

**Solution Option 3**: Enable C23 mode
```cmake
set(CMAKE_C_STANDARD 23)
```

**Recommended**: Option 1 (quick), verify Option 3 viability for Phase 5

**Verification**:
```bash
cmake -S . -B build_clean -G Ninja -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_C_FLAGS="-Werror -Wno-gnu-include-next -Wno-c23-extensions"
ninja -C build_clean kernel
```

**Expected result**: Build succeeds, reveals next tier of warnings

---

### PHASE 4B: Core Kernel File Integration (HIGH IMPACT - 3-4 days)

**WHY**: 972 lines of critical kernel code currently excluded. Re-enabling adds VFS, IPC, memory zones.

**WHAT**: Re-enable stubs.c, zone.c, endpoint.c, zone_isolation.c with exact dependency fixes

**DEPENDENCIES RESOLVED**: Agent exploration verified all dependencies exist:
- ksleep/wakeup declared in include/defs.h lines 167, 170
- KERNBASE/PHYSTOP/KERNSIZE defined in include/memlayout.h
- cap_validate_unified() exists but needs public declaration

#### Task 4: Integrate stubs.c + zone.c (Parallel - LOW complexity)
**Files**:
- `kernel/stubs.c` (394 lines) - VFS operations
- `kernel/mem/zone.c` (100 lines) - Slab allocator

**Status**: READY - No dependencies to fix

**stubs.c provides**:
- VFS: fileinit(), filealloc(), filedup(), fileclose(), fileread(), filewrite(), filestat()
- Legacy sleep() wrapper calling ksleep()

**zone.c provides**:
- zone_create(), zone_alloc(), zone_free(), zone_dump()

**Implementation**:
1. Remove both from exclusion list in kernel/CMakeLists.txt (lines 133, 127)
2. Build and verify

**Verification**:
```bash
nm build/kernel/kernel | grep -E "file_|zone_"
# Expected: filealloc, fileclose, fileread, filewrite, zone_alloc, zone_free
```

#### Task 5: Integrate zone_isolation.c (MEDIUM complexity)
**File**: `kernel/mem/zone_isolation.c` (493 lines)

**Dependencies to fix**:
1. Change `#include "vm.h"` to `#include "memlayout.h"` (line 9)
2. Add cap_validate_unified() declaration to include/cap.h

**Implementation**:
```c
// In include/cap.h, add:
typedef enum {
    VALIDATION_SUCCESS,
    VALIDATION_FAILED,
    VALIDATION_INVALID_ID,
    VALIDATION_EPOCH_MISMATCH
} cap_validation_result_t;

cap_validation_result_t cap_validate_unified(cap_id_t id, struct cap_entry *out_entry_if_valid);
```

Then edit zone_isolation.c:
```c
// Line 9, change:
#include "vm.h"  // OLD
#include "memlayout.h"  // NEW
```

**Verification**:
```bash
nm build/kernel/kernel | grep zone_isolation
# Expected: zone_isolation_init, zone_isolation_alloc, cross_zone_transfer
```

#### Task 6: Integrate endpoint.c (LOW complexity)
**File**: `kernel/ipc/endpoint.c` (85 lines)

**Dependencies**: None (ksleep/wakeup already available)

**Needs**: Syscall registration in kernel/syscall.c

**Implementation**:
1. Remove from exclusion list (line 151)
2. Add syscall entries to kernel/syscall.c syscall table:
```c
[SYS_endpoint_send]   sys_endpoint_send,
[SYS_endpoint_recv]   sys_endpoint_recv,
```

**Verification**:
```bash
nm build/kernel/kernel | grep endpoint
# Expected: sys_endpoint_send, sys_endpoint_recv, endpoint_create
```

**Expected Outcome**: 972 lines of critical kernel code re-enabled (stubs: 394, zone.c: 100, endpoint: 85, zone_isolation: 493)

---

### PHASE 4C: Documentation Completion (MEDIUM - 2-3 days)

**WHY**: Recent changes (lambda_cap, Conan, Rocq proofs) lack user-facing documentation

**WHAT**: Create guides for lambda_cap usage, Conan workflow, testing strategy

#### Task 7: Lambda Capability User Guide
**File**: `docs/LAMBDA_CAP_GUIDE.md` (NEW)

**Contents**:
1. Overview of linear capability semantics
2. When to use lambda_cap vs regular capabilities
3. Code examples: create, use, delegate, revoke
4. Energy accounting and fuel mechanics
5. Integration with pi-calculus process algebra
6. Formal verification guarantees (reference LambdaCap.v)

**Verification**: Technical reviewer can implement lambda_cap-based system from docs

#### Task 8: Conan Build Documentation
**File**: `docs/CONAN_USAGE.md` (NEW)

**Contents**:
1. Installing Conan 2.x
2. Building with default profile: `conan install . -pr:h profiles/default`
3. Building kernel with freestanding profile
4. Creating lockfile for reproducibility: `conan lock create .`
5. Using in CI/CD pipelines
6. Adding dependencies to conanfile.py

**Verification**: New contributor can build using Conan from scratch

#### Task 9: Testing Strategy Documentation
**File**: `docs/TESTING_STRATEGY.md` (NEW)

**Contents**:
1. Test framework overview (C17 custom, pytest, BATS)
2. Running tests locally: `ctest --output-on-failure`
3. Test categories: unit, integration, POSIX, personality
4. Adding new tests
5. Coverage requirements (40% minimum)
6. CI pipeline test matrix
7. QEMU kernel boot validation

**Verification**: Developer can add tests and run full suite locally

#### Task 10: Clean Up Duplicate Files
**Files**: Remove files with " 2" suffix

**Action**: Remove or consolidate these duplicates:
- `docs/design/EXOKERNEL_SYNTHESIS_2024 2.md`
- `docs/planning/ROADMAP_2025 2.md`
- `docs/setup/setup 2.md`
- 7 other " 2" duplicate files

**Verification**: `find docs -name "* 2.md" | wc -l` returns 0

---

### PHASE 4D: Performance & Quality Baselines (LOW-MEDIUM - 2-3 days)

**WHY**: No performance regression detection or quality enforcement

**WHAT**: Baseline microbenchmarks, enforce coverage, add static analysis

#### Task 11: Baseline Performance Metrics
**Files**:
- `tests/microbench/baseline_metrics.json` (NEW)
- `.github/workflows/feuerbird_ci.yml` (ADD benchmark job)

**Implementation**:
1. Run all microbenchmarks, record results
2. Store in `baseline_metrics.json`
3. In CI, compare current run to baseline
4. Fail if >10% regression

**Metrics to baseline**:
- cap_verify latency
- exo_yield_to context switch time
- lattice_pipe throughput
- IPC round-trip time

**Verification**: Intentionally slow a benchmark, verify CI fails

#### Task 12: Static Analysis in CI
**Files**: `.github/workflows/feuerbird_ci.yml`

**Add job**:
```yaml
- name: Static Analysis
  run: |
    ninja -C build clang-tidy
    if [ -f build/clang-tidy-report.txt ]; then
      if grep -q "error:" build/clang-tidy-report.txt; then
        cat build/clang-tidy-report.txt
        exit 1
      fi
    fi
```

**Verification**: Introduce a bug clang-tidy catches, verify CI fails

---

## Task Breakdown & Time Estimates

| Phase | Tasks | Time | Priority | Status |
|-------|-------|------|----------|--------|
| 4A: Testing | T1-T3 | 2-3 days | CRITICAL | ✅ COMPLETE |
| 4B-Pre: Warnings | T4-Pre, T5-Pre | 1-2 days | CRITICAL | ❌ Not started |
| 4B: Integration | T4-T6 | 3-4 days | HIGH | ❌ Not started |
| 4C: Documentation | T7-T10 | 2-3 days | MEDIUM | ❌ Not started |
| 4D: Baselines | T11-T12 | 2-3 days | MEDIUM | ❌ Not started |
| **PHASE 4 TOTAL** | **15 tasks** | **11-16 days** | - | **1/15 complete** |

---

## Critical Files Matrix

| File | Action | Tasks | Lines |
|------|--------|-------|-------|
| `.github/workflows/feuerbird_ci.yml` | EDIT | T1,T2,T3,T11,T12 | ~150 |
| `kernel/boot/main64.c` | EDIT | T2 | ~10 |
| `kernel/defs.h` | EDIT | T4 | ~5 |
| `kernel/CMakeLists.txt` | EDIT | T4,T5,T6 | ~20 |
| `include/vm.h` | CREATE | T6 | ~30 |
| `docs/LAMBDA_CAP_GUIDE.md` | CREATE | T7 | ~200 |
| `docs/CONAN_USAGE.md` | CREATE | T8 | ~150 |
| `docs/TESTING_STRATEGY.md` | CREATE | T9 | ~200 |
| `tests/microbench/baseline_metrics.json` | CREATE | T11 | ~50 |

---

## Verification Checklist

### Testing (Phase 4A)
- [ ] CI fails when pytest has failures
- [ ] CI fails when ctest has failures
- [ ] Kernel boot prints KERNEL_BOOT_SUCCESS marker
- [ ] QEMU test validates boot marker presence
- [ ] Coverage report generated with ≥40% coverage
- [ ] Coverage job uploads to codecov

### Integration (Phase 4B)
- [ ] `kernel/stubs.c` builds and links
- [ ] VFS functions visible: `nm build/kernel/kernel | grep file_`
- [ ] `kernel/ipc/endpoint.c` builds and links
- [ ] Endpoint functions visible: `nm build/kernel/kernel | grep endpoint`
- [ ] `include/vm.h` exists with memory constants
- [ ] `kernel/mem/zone.c` builds and links
- [ ] Zone allocator visible: `nm build/kernel/kernel | grep zone_`
- [ ] Kernel binary size increases (more functionality integrated)

### Documentation (Phase 4C)
- [ ] `docs/LAMBDA_CAP_GUIDE.md` exists
- [ ] Lambda_cap examples compile
- [ ] `docs/CONAN_USAGE.md` exists
- [ ] Conan workflow tested by following docs
- [ ] `docs/TESTING_STRATEGY.md` exists
- [ ] Test instructions verified by running locally
- [ ] No files with " 2" suffix in docs/

### Baselines (Phase 4D)
- [ ] `tests/microbench/baseline_metrics.json` exists
- [ ] Benchmark regression check runs in CI
- [ ] Static analysis job exists in CI
- [ ] clang-tidy errors fail the build

---

## Risk Mitigation

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Enabling tests breaks CI | HIGH | HIGH | Fix tests before enforcing |
| Coverage too low initially | MEDIUM | MEDIUM | Start at 30%, raise to 40% |
| Zone integration causes conflicts | MEDIUM | MEDIUM | Careful vm.h design |
| Performance baselines too strict | LOW | MEDIUM | 10% tolerance initially |

---

## Dependencies & Prerequisites

### Required Tools
- LLVM 21+ (for coverage, clang-tidy)
- CMake 3.20+
- Ninja
- pytest
- QEMU 8.0+

### External Dependencies
- codecov account for coverage upload (optional but recommended)
- GitHub Actions runner with sufficient disk space

### Knowledge Requirements
- Understanding of CMake test integration (CTest)
- Basic QEMU usage for kernel testing
- GitHub Actions YAML syntax

---

## PHASE 5: Advanced Integration & Production Readiness (5-8 weeks)

### Overview

Phase 5 integrates foundational capability system, advanced IPC, and production features. Divided into 3 sub-phases:
- **5A: Critical Functionality** (2-3 weeks) - Unblocks core systems
- **5B: Advanced Features** (2-3 weeks) - Quality and performance
- **5C: Polish & Distribution** (1-2 weeks) - Production deployment

---

### PHASE 5A: Critical Functionality (FOUNDATIONAL - 2-3 weeks)

**WHY**: Capability lattice is foundational for security model. Exo_impl provides core exokernel layer.

**WHAT**: Integrate capability_lattice.c, exo_impl.c, complete personality tests, architecture docs

#### Task 5A-1: Integrate capability_lattice.c (3-4 days)
**File**: `kernel/capability/capability_lattice.c` (600 lines)

**Provides**:
- Complete capability system with 20+ rights, 13 types
- Lattice operations (join, meet, dominance)
- HMAC-SHA256 authentication with nonces
- 256-byte cache-aligned capabilities (65,536 slots)

**Dependencies to fix**:
- Implement `hal_read_timestamp()` (hardware abstraction layer)
- Replace placeholder HMAC with real crypto (or integrate libsodium)

**Implementation**:
1. Create `include/hal_timestamp.h` with RDTSC wrapper
2. Link crypto library or implement HMAC-SHA256
3. Enable capability/ subdirectory in CMakeLists.txt
4. Test lock-free operations under load

**Verification**:
```bash
nm build/kernel/kernel | grep -E "cap_create|cap_derive|cap_check|cap_revoke"
```

#### Task 5A-2: Integrate exo_impl.c (2-3 days)
**File**: `kernel/exo_impl.c` (687 lines)

**Provides**:
- CPU operations, IRQ binding, DMA allocation
- Beatty and DAG schedulers
- Fast IPC syscall
- Kernel math utilities

**Dependencies to fix**:
- Fix type mismatches in `exo_sched_ops` structure
- Validate atomic operations

**Implementation**:
1. Audit `exo_sched_ops` type definitions
2. Fix pointer type mismatches
3. Remove from exclusion list
4. Test scheduler switching

#### Task 5A-3: Complete Personality Tests (2-3 days)
**Expand**: `tests/personality/` suite

**Add**:
- Illumos-specific syscall tests
- Cross-personality IPC tests
- BSD compat layer validation
- Automated CI integration

#### Task 5A-4: Architecture Documentation (2-3 days)
**Create**:
- `docs/CAPABILITY_LATTICE_ARCHITECTURE.md` - Security model, lattice theory
- `docs/IPC_ARCHITECTURE.md` - Message passing dataflow, serialization
- `docs/BOOT_SEQUENCE.md` - From multiboot2 to userspace init

---

### PHASE 5B: Advanced Features (QUALITY - 2-3 weeks)

**WHY**: Secure IPC with crypto, fuzzing for code quality, PGO for performance

**WHAT**: lattice_kernel.c, serialization.c, fuzzing, PGO/LTO, API docs

#### Task 5B-1: Integrate lattice_kernel.c (3-4 days)
**File**: `kernel/ipc/lattice_kernel.c` (400 lines)
**Depends on**: capability_lattice.c (5A), exo_impl.c (5A)

**Provides**:
- Lattice-based IPC with 16 levels, 256 dimensions
- Simplified Kyber post-quantum crypto
- Gas accounting for IPC operations

**Implementation**:
1. Verify capability_lattice and exo_impl integrated
2. Integrate Kyber polynomial operations
3. Test gas limits prevent DoS
4. Benchmark IPC throughput

#### Task 5B-2: Integrate serialization.c (2 days)
**File**: `kernel/ipc/serialization.c` (300 lines)

**Provides**:
- Raw (zero overhead memcpy)
- Cap'n Proto Lite (header + XOR checksum)
- Cap'n Proto Full (complete protocol)

**Implementation**:
1. Create `ipc/serialization.h`
2. Verify Cap'n Proto helpers exist
3. Benchmark all 3 modes

#### Task 5B-3: Syscall Fuzzing Infrastructure (3-4 days)
**Create**: Fuzzing harness with AFL++

**Implementation**:
1. Install AFL++
2. Create syscall harness in `tests/fuzzing/`
3. Fuzz capability operations (create, derive, revoke)
4. Fuzz IPC operations (send, recv, endpoints)
5. Run with ASAN + UBSAN
6. Add to CI (nightly fuzzing runs)

#### Task 5B-4: Performance Optimization (3-4 days)
**Enable**: PGO (Profile-Guided Optimization) and LTO

**Implementation**:
1. Add PGO build profile to CMakeLists.txt
2. Collect profiles from benchmarks
3. Rebuild with PGO
4. Enable LTO for Release builds
5. Add regression tests to CI

#### Task 5B-5: API Documentation (3-4 days)
**Setup**: Doxygen extraction

**Create**:
- `docs/SYSCALL_API_REFERENCE.md`
- `docs/CAPABILITY_API_REFERENCE.md`
- `docs/IPC_API_REFERENCE.md`
- `docs/LIBOS_API_REFERENCE.md`

---

### PHASE 5C: Polish & Distribution (PRODUCTION - 1-2 weeks)

**WHY**: Linux compatibility, easy installation, production deployment

**WHAT**: procfs.c, ISO creation, deployment docs, CI enhancements

#### Task 5C-1: Integrate procfs.c (3-4 days)
**File**: `kernel/fs/procfs.c` (500 lines)
**Depends on**: VFS layer (Phase 4B)

**Provides**:
- Personality-aware /proc and /sys
- /proc/[pid]/status, maps, cmdline
- /sys/kernel/hostname, /sys/devices

#### Task 5C-2: GRUB ISO Creation (2-3 days)
**Create**: Bootable ISO infrastructure

**Implementation**:
1. Create `scripts/create_iso.sh`
2. GRUB2 config in `boot/grub/grub.cfg`
3. Test QEMU boot from ISO
4. Add ISO build to CI

#### Task 5C-3: Deployment Documentation (2-3 days)
**Create**:
- `docs/BARE_METAL_DEPLOYMENT.md`
- `docs/ISO_INSTALLATION.md`
- `docs/TROUBLESHOOTING.md`
- `docs/SECURITY_HARDENING.md`

#### Task 5C-4: CI/CD Enhancements (2 days)
**Add to CI**:
- ISO build job
- Nightly fuzzing runs
- Performance tracking (store metrics)
- Documentation generation (Doxygen)

---

## Appendix: Excluded Files for Future Integration

### Tier 2 Integration Candidates (After Phase 4)

| File | Lines | Complexity | Impact |
|------|-------|------------|--------|
| exo_impl.c | 687 | MEDIUM | Core exokernel functions |
| serialization.c | ~300 | MEDIUM | IPC serialization |
| lattice_kernel.c | ~400 | MEDIUM | Capability lattice |
| procfs.c | ~500 | MEDIUM-HIGH | Linux /proc compatibility |
| capability_lattice.c | ~600 | HIGH | Security lattice |

### Files to Permanently Exclude

- `waitchan.c` - Conflicts with proc.c scheduler
- `zerocopy_cow_dag.c` - Research prototype
- `quantum_lock.*` - Experimental (archived)
- `genetic_lock_*` - Experimental (archived)
- `ultimate_lock_*` - Experimental (archived)
- `unified_lock.*` - Superseded by ticketlock

---

## Phase 5 Time Estimates

| Phase | Tasks | Time | Priority |
|-------|-------|------|----------|
| 5A: Critical | 4 tasks | 2-3 weeks | CRITICAL |
| 5B: Advanced | 5 tasks | 2-3 weeks | HIGH |
| 5C: Polish | 4 tasks | 1-2 weeks | MEDIUM |
| **PHASE 5 TOTAL** | **13 tasks** | **5-8 weeks** | - |

---

## COMPREHENSIVE TODO LIST (Granular Execution Plan)

### IMMEDIATE NEXT STEPS (Phase 4B-Pre: Warning Resolution)

**Week 1: Fix Build-Blocking Warnings**

1. [ ] Add `-Wno-gnu-include-next` to CMakeLists.txt
2. [ ] Add `-Wno-c23-extensions` to CMakeLists.txt
3. [ ] Test build with `-Werror` succeeds
4. [ ] Document workarounds in cmake/CompilerWarnings.cmake
5. [ ] Create GitHub issue to track proper header refactoring (Phase 5)

**Expected outcome**: Clean build with -Werror, reveals tier 2 warnings

### PHASE 4B: Integration (Week 2-3)

**Task 4: stubs.c + zone.c**
6. [ ] Edit kernel/CMakeLists.txt - remove stubs.c from exclusion (line 133)
7. [ ] Edit kernel/CMakeLists.txt - remove zone.c from exclusion (line 127)
8. [ ] Build: `ninja -C build kernel`
9. [ ] Verify symbols: `nm build/kernel/kernel | grep -E "file_|zone_"`
10. [ ] Test VFS operations available

**Task 5: zone_isolation.c**
11. [ ] Edit include/cap.h - add cap_validation_result_t enum
12. [ ] Edit include/cap.h - add cap_validate_unified() declaration
13. [ ] Edit kernel/mem/zone_isolation.c line 9 - change vm.h to memlayout.h
14. [ ] Edit kernel/CMakeLists.txt - remove zone_isolation.c exclusion
15. [ ] Build and verify: `nm build/kernel/kernel | grep zone_isolation`

**Task 6: endpoint.c**
16. [ ] Edit kernel/CMakeLists.txt - remove endpoint.c exclusion (line 151)
17. [ ] Edit kernel/syscall.c - add SYS_endpoint_send entry
18. [ ] Edit kernel/syscall.c - add SYS_endpoint_recv entry
19. [ ] Build and verify: `nm build/kernel/kernel | grep endpoint`

**Integration Verification**
20. [ ] Kernel size increased (972+ lines added)
21. [ ] All symbols present (filealloc, zone_alloc, endpoint_create, etc.)
22. [ ] No linker errors
23. [ ] Commit with message: "feat(kernel): Integrate VFS, IPC, memory zones"

### PHASE 4C: Documentation (Week 3-4)

**Task 7: Lambda Capability Guide**
24. [ ] Create docs/LAMBDA_CAP_GUIDE.md
25. [ ] Write sections: Overview, Usage, Examples, Energy, Pi-calculus, Verification
26. [ ] Add code examples that compile
27. [ ] Technical review

**Task 8: Conan Usage Guide**
28. [ ] Create docs/CONAN_USAGE.md
29. [ ] Document installation, profiles, lockfile, CI usage
30. [ ] Test workflow from docs
31. [ ] Add to docs/README.md index

**Task 9: Testing Strategy Guide**
32. [ ] Create docs/TESTING_STRATEGY.md
33. [ ] Document frameworks, local testing, categories, coverage
34. [ ] Add examples of adding new tests
35. [ ] Verify instructions work

**Task 10: Clean Duplicate Files**
36. [ ] Find all " 2.md" files: `find docs -name "* 2.md"`
37. [ ] Review each for unique content
38. [ ] Consolidate or delete duplicates
39. [ ] Verify: `find docs -name "* 2.md" | wc -l` returns 0

### PHASE 4D: Baselines (Week 4-5)

**Task 11: Performance Baselines**
40. [ ] Run all microbenchmarks: `ninja -C build benchmark`
41. [ ] Record results to tests/microbench/baseline_metrics.json
42. [ ] Create CI job for benchmark comparison
43. [ ] Set 10% regression threshold
44. [ ] Test with intentional slowdown

**Task 12: Static Analysis**
45. [ ] Add clang-tidy target to CMakeLists.txt
46. [ ] Create .clang-tidy config
47. [ ] Add CI job for static analysis
48. [ ] Fix critical warnings
49. [ ] Commit fixes

### PHASE 5A: Critical Functionality (Week 6-9)

**Task 5A-1: capability_lattice.c**
50. [ ] Create include/hal_timestamp.h with RDTSC
51. [ ] Implement or link HMAC-SHA256
52. [ ] Enable capability/ in CMakeLists.txt
53. [ ] Build and test
54. [ ] Load test lock-free operations

**Task 5A-2: exo_impl.c**
55. [ ] Audit exo_sched_ops structure
56. [ ] Fix type mismatches
57. [ ] Remove from exclusion list
58. [ ] Test scheduler switching
59. [ ] Verify atomic operations

**Task 5A-3: Personality Tests**
60. [ ] Add Illumos syscall tests
61. [ ] Add cross-personality IPC tests
62. [ ] Add BSD compat tests
63. [ ] Integrate into CI

**Task 5A-4: Architecture Docs**
64. [ ] Write CAPABILITY_LATTICE_ARCHITECTURE.md
65. [ ] Write IPC_ARCHITECTURE.md
66. [ ] Write BOOT_SEQUENCE.md

### PHASE 5B: Advanced Features (Week 10-13)

**Tasks 5B-1 through 5B-5**: (13 detailed subtasks - see plan)

### PHASE 5C: Polish (Week 14-16)

**Tasks 5C-1 through 5C-4**: (12 detailed subtasks - see plan)

---

## PLAN STATUS

**Phase 4A**: ✅ COMPLETE (3/15 Phase 4 tasks)
**Phase 4B-Pre**: ❌ NOT STARTED (Warning resolution)
**Phase 4B**: ❌ NOT STARTED (Integration)
**Phase 4C**: ❌ NOT STARTED (Documentation)
**Phase 4D**: ❌ NOT STARTED (Baselines)
**Phase 5**: ❌ NOT STARTED

**Estimated Duration**:
- Phase 4 remainder: 10-13 days (2-3 weeks)
- Phase 5: 5-8 weeks
- **Total: 7-11 weeks from now**

**Estimated Effort**: ~280-440 hours total

---

**Plan Approval Status**: Ready for user approval
**Next Action**: Begin Phase 4B-Pre (Warning Resolution) upon approval
