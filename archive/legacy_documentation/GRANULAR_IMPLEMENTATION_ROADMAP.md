# GRANULAR IMPLEMENTATION ROADMAP - ExoKernel v6
## Systematic Per-File, Per-Function Build Plan

Generated: 2025-09-02  
Based on: Deep technical debt audit + Build dependency analysis
Target: Working POSIX-2024 compliant ExoKernel

---

## CRITICAL PATH EXECUTIVE SUMMARY

**Phase 1**: Fix 4 header location issues (2-3 days)
**Phase 2**: Build minimal working kernel (1-2 weeks)  
**Phase 3**: Implement 23 critical POSIX utilities (3-4 weeks)
**Phase 4**: Security and optimization (4-6 weeks)

**Total Estimate**: 10-15 weeks for production-ready system

---

## PHASE 1: FOUNDATION FIXES (WEEK 1)
### Critical Blocker Resolution

#### 1.1 Header Location Fixes (Day 1-2)
```bash
# File moves required:
mv exo.h kernel/exo.h                    # Fix kernel/proc.h includes
```

**Files to Modify:**
- `kernel/proc.h:8` → Update `#include "exo.h"` path
- `kernel/defs.h` → Verify include paths
- `Makefile` → Update include flags to `-I./include -I./kernel`

#### 1.2 Header Conflict Resolution (Day 2-3)  
**Duplicate Resolution:**
- `include/types.h` vs `kernel/types.h` → Keep include/types.h (more complete)
- Remove `kernel/types.h` and update kernel files to use include/types.h

**Architecture Headers:**
- `include/x86.h` → Create `include/arch.h` with ARM64 compatibility
- Update all x86.h references to arch.h

#### 1.3 Build System Validation (Day 3)
**Test Sequence:**
```bash
gcc -MM -I./include -I./kernel user/cp.c     # Should work
gcc -MM -I./include -I./kernel kernel/proc.c # Should work after fixes
make mkfs                                     # Should still work
```

---

## PHASE 2: MINIMAL WORKING KERNEL (WEEKS 2-3)
### Core Exokernel Implementation

#### 2.1 Replace kernel_stub.c (Week 2, Days 1-3)
**File**: `kernel_stub.c` → Real kernel implementation

**Functions to Implement:**
```c
// kernel/main.c (NEW FILE)
void kmain(void)                    // Kernel entry point
void kernel_init(void)              // Initialize core systems
void scheduler_init(void)           // Basic scheduler
void memory_init(void)              // Memory management init
```

**Dependencies**: 
- Fix `kernel/proc.c` compilation first
- Implement basic `kernel/vm.c` memory management
- Create working `kernel/syscall.c`

#### 2.2 Essential Syscall Infrastructure (Week 2, Days 4-5)
**File**: `kernel/exo.c` (currently stub syscalls)

**Priority 1 Syscalls:**
```c
int sys_exit(int status)            // Process termination
int sys_fork(void)                  // Process creation  
int sys_exec(char *path, char **argv) // Program execution
int sys_write(int fd, void *buf, int n) // Basic I/O
int sys_read(int fd, void *buf, int n)  // Basic I/O
```

**Implementation Strategy**: 
- Start with minimal implementations that don't crash
- Add proper error handling incrementally
- Test with simple user programs

#### 2.3 Boot Sequence (Week 3, Days 1-2)
**Files to Create/Modify:**
- `bootasm.S` → Boot sector that actually loads kernel
- `entry.S` → Kernel entry point assembly
- `kernel/main.c` → C kernel entry

**Boot Requirements:**
- Set up basic page tables
- Initialize GDT/IDT
- Jump to kernel main()
- Print "ExoKernel v6 booting..." message

#### 2.4 Basic Memory Management (Week 3, Days 3-5)
**File**: `kernel/vm.c` (has existing structure, needs real implementation)

**Critical Functions:**
```c
void vm_init(void)                  // Initialize virtual memory
char* kalloc(void)                  // Kernel memory allocation
void kfree(char *v)                 // Kernel memory free
pde_t* setupkvm(void)               // Set up kernel virtual memory
```

**Success Criteria**: Kernel boots and runs hello world user program

---

## PHASE 3: CRITICAL POSIX UTILITIES (WEEKS 4-7)
### Priority-Ordered Implementation

#### 3.1 System Essential Utilities (Week 4)
**Priority 1 - System Core:**

1. **user/sh.c** (Shell - Most Critical)
   - Functions: `main()`, `parsecmd()`, `runcmd()`, `exec()`, `pipe()`
   - Dependencies: Working `sys_exec`, `sys_fork`, `sys_wait`
   - Test: `echo hello | wc`

2. **user/echo_real.c** → **user/echo.c** 
   - Replace stub with: `main(int argc, char *argv[])` 
   - Implementation: Print arguments with optional -n flag
   - Test: `echo "hello world"`

3. **user/cat_real.c** → **user/cat.c**
   - Functions: `main()`, `cat(int fd)`
   - Dependencies: Working `sys_read`, `sys_write`
   - Test: `cat /README`

4. **user/pwd_real.c** → **user/pwd.c** 
   - Functions: `main()`, `getcwd(char *buf, size_t size)`
   - Current stub at line 140: "xv6 doesn't have symlinks, so this is a stub"
   - Implementation: Real directory tracking

5. **user/test_real.c** → **user/test.c**
   - Functions: `main()`, `evaluate()`, `test_file()`, `test_string()`
   - Critical for shell scripting
   - Test: `test -f /bin/sh && echo exists`

#### 3.2 File Management Utilities (Week 5)
**Priority 2 - File Operations:**

6. **user/chmod.c** (Security Critical)
   - Current: Line 125 "For now, this is a stub"
   - Functions: `main()`, `change_mode(char *path, mode_t mode)`
   - Dependencies: Working filesystem syscalls
   - Test: `chmod 755 /bin/sh`

7. **user/who.c** (System Information)
   - Current: Line 313 "Stub - would call kernel" 
   - Functions: `main()`, `get_utmp_info()`, `format_user_info()`
   - Test: `who`

8. **user/realpath.c** (Path Resolution)
   - Current: Line 520 "Stub - would call kernel"
   - Functions: `main()`, `resolve_path(char *path)`
   - Critical for shell operations
   - Test: `realpath /bin/../bin/sh`

#### 3.3 Text Processing Core (Week 6)
**Priority 3 - Text Manipulation:**

9. **user/join.c** (File Joining)
   - Current: Line 15 "Stub implementation - would join files on common field"
   - Functions: `main()`, `join_files()`, `find_common_field()`
   - Test: `join file1 file2`

10. **user/fold.c** (Line Wrapping)
    - Current: Line 17 "Stub implementation - would wrap lines at specified width"
    - Functions: `main()`, `wrap_lines(int width)`
    - Test: `echo "very long line" | fold -w 10`

11. **user/csplit.c** (File Splitting)
    - Current: Line 15 "Stub implementation - would split file at pattern boundaries"
    - Functions: `main()`, `split_at_pattern()`, `write_section()`
    - Test: `csplit file.txt /pattern/`

#### 3.4 Advanced Text Processing (Week 7)
**Priority 4 - Complex Text Tools:**

12. **user/awk.c** (Text Processing Engine)
    - Current: Line 439 "Stub functions"
    - Major implementation effort
    - Functions: `main()`, `parse_program()`, `execute_pattern()`, `built_in_functions()`
    - Test: `echo "1 2 3" | awk '{print $1 + $2}'`

13. **user/diff.c** (File Comparison)
    - Current: Lines 477, 482 "Stub - would use real mmap", "Stub"
    - Functions: `main()`, `compare_files()`, `output_diff()`
    - Test: `diff file1 file2`

14. **user/patch.c** (File Patching)
    - Current: Lines 588, 594 "Stub - would implement rename", "Stub"
    - Functions: `main()`, `apply_patch()`, `validate_patch()`
    - Test: `patch < changes.diff`

---

## PHASE 4: SECURITY AND LIBOS (WEEKS 8-11)
### System Hardening and Advanced Features

#### 4.1 Cryptographic Security (Week 8-9)
**File**: `kernel/crypto.c` (CRITICAL SECURITY ISSUE)

**Current Issues**:
- Line 8: "NOT CRYPTOGRAPHICALLY SECURE"
- Line 25: "STUB: Simple non-secure derivation"
- Line 29: "Temporary: Print a warning that a stub is being used"

**Implementation Required**:
```c
// Replace stub implementations:
int libos_kdf_derive(const uint8_t *input, size_t input_len, 
                     uint8_t *output, size_t output_len)

// Add secure implementations:
int secure_random_bytes(uint8_t *buf, size_t len)
int secure_hash_sha256(const uint8_t *input, size_t len, uint8_t *output)
int secure_hmac(const uint8_t *key, size_t key_len, 
                const uint8_t *data, size_t data_len, uint8_t *output)
```

#### 4.2 Post-Quantum IPC (Week 9-10)
**File**: `kernel/lattice_ipc.c` (Multiple TODO items)

**Critical TODOs to Implement**:
- Line 53: "Replace pqcrypto_kem_keypair with robust, audited implementation"
- Line 57: "Add robust error handling for exo_send/exo_recv"
- Line 66: "Replace pqcrypto_kem_enc with robust implementation"
- Line 77: "Replace pqcrypto_kem_dec with robust implementation"  
- Line 85: "Replace libos_kdf_derive with robust KDF implementation"

**Functions to Implement**:
```c
int lattice_key_exchange(struct exo_cap *ep1, struct exo_cap *ep2)
int lattice_secure_send(struct exo_cap *ep, const void *data, size_t len)
int lattice_secure_recv(struct exo_cap *ep, void *data, size_t max_len)
```

#### 4.3 Signal Handling (Week 10)
**File**: `libos/signal_posix.c` (POSIX Critical)

**TODO Implementation**:
- Line 261: "TODO: Implement timeout" in signal wait
- Line 340: "TODO: Stop process"  
- Line 343: "TODO: Continue process"

**Functions to Complete**:
```c
int sigtimedwait(const sigset_t *set, siginfo_t *info, 
                 const struct timespec *timeout)
int kill_stop_process(pid_t pid)
int kill_continue_process(pid_t pid)
```

#### 4.4 LibOS Filesystem (Week 11)
**File**: `libos/fs.c` (User-space FS)

**Current**: Line 8 "Simplified user-space filesystem stubs"

**Implementation Required**:
```c
int libos_open(const char *path, int flags, mode_t mode)
ssize_t libos_read(int fd, void *buf, size_t count)
ssize_t libos_write(int fd, const void *buf, size_t count)
int libos_close(int fd)
off_t libos_lseek(int fd, off_t offset, int whence)
int libos_stat(const char *path, struct stat *buf)
```

---

## PHASE 5: ADVANCED FEATURES (WEEKS 12-15)
### Performance and Virtualization

#### 5.1 Hypervisor Implementation (Week 12)
**File**: `kernel/hypervisor/hypervisor.c`

**Current Issues**:
- Line 3: "Minimal hypervisor capability stubs"
- Line 13: "Allocate a Hypervisor capability (stub)"
- Line 23: "hv_launch_guest: stub. Cap ID=%u, path=%s"

#### 5.2 Network Services (Week 13)
**File**: `user/ping.c`

**Current Stubs** (Lines 514, 520, 526):
```c
// Line 514: "Stub - would create raw socket"
// Line 520: "Stub - would send packet"  
// Line 526: "Stub - would receive packet"
```

#### 5.3 Development Tools (Week 14-15)
**Files**: `user/gdb.c`, `user/valgrind.c`, `user/objdump.c`

**Implementation Priority**: Lower (development aids)

---

## TESTING AND VALIDATION STRATEGY

### Unit Testing (Each Phase)
```bash
# Phase 1: Build System
make clean && make mkfs && ./mkfs

# Phase 2: Kernel  
make qemu  # Should boot and run hello

# Phase 3: POSIX Utilities
./scripts/test_our_posix_utilities.sh

# Phase 4: Security
./scripts/run_security_tests.sh

# Phase 5: Integration
make posix_compliance_test && ./posix_compliance_test
```

### Success Metrics
- **Phase 1**: 95% files compile without header errors
- **Phase 2**: Kernel boots in QEMU, runs hello world
- **Phase 3**: 23/23 critical POSIX utilities working  
- **Phase 4**: Zero security stubs, all crypto real
- **Phase 5**: Full POSIX-2024 compliance test suite passes

---

## RESOURCE REQUIREMENTS

### Development Tools
- Cross-compilation toolchain (if targeting x86_64)
- QEMU for testing (qemu-system-x86_64)
- Static analysis tools (clang-analyzer)
- Cryptographic libraries (libsodium recommended)

### Time Allocation
- **50%**: Core kernel functionality (Phases 1-2)
- **30%**: POSIX utilities implementation (Phase 3)  
- **15%**: Security hardening (Phase 4)
- **5%**: Advanced features (Phase 5)

### Risk Mitigation
- **Build Breaks**: Fix incrementally, test at each step
- **Crypto Complexity**: Use established libraries vs custom implementation
- **POSIX Compliance**: Reference existing implementations (busybox, GNU coreutils)
- **Performance**: Optimize only after correctness achieved

---

**Bottom Line**: This roadmap provides a systematic path from current broken state to full POSIX-2024 compliant ExoKernel. Critical path is 4 header fixes → minimal kernel → 23 core utilities → security hardening. Total effort: 10-15 weeks with proper execution.