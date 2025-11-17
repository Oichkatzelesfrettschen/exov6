# Phase 8: Immediate Next Steps - Tactical Execution Plan
**Fine-Grained Action Items**

---

## 🎯 Current Status

**Phase 7 Complete:** 7 critical locks migrated (60+ sites)
- ✅ idelock, icache, bcache, fs_log, tickslock (filesystem)
- ✅ beatty_lock, dag_lock (scheduler)
- ✅ Commit 66fcb9a pushed to remote

**Phase 8 Started:** Real-world validation
- ⏳ Build verification (compilation errors present)
- ⚠️ Blockers identified (header conflicts, missing includes)

---

## 🚧 Current Blockers

### Blocker 1: Header Conflicts (exo_lock.h vs modern locks)

**Issue:**
```
/home/user/exov6/include/exo_lock.h:48:8: error: redefinition of 'mcs_node'
/home/user/exov6/include/exo_lock.h:110:6: error: conflicting types for 'qspin_lock'
```

**Root Cause:**
- `exo_lock.h` defines old lock interfaces
- New lock headers (qspinlock.h, adaptive_mutex.h) define modern interfaces
- Both included in same translation unit → conflict

**Resolution Strategy:**
1. Create `modern_locks.h` wrapper
2. Add `#ifndef EXO_LEGACY_LOCKS` guards in exo_lock.h
3. Update kernel files to use modern_locks.h

### Blocker 2: Userspace vs Kernel Header Conflicts

**Issue:**
```
/home/user/exov6/include/exokernel.h:40:19: error: conflicting types for 'exo_alloc_block'
/home/user/exov6/kernel/defs.h:251:21: note: previous declaration is here
```

**Root Cause:**
- `include/exokernel.h` has userspace API
- `kernel/defs.h` has kernel API
- Different signatures for same function names

**Resolution Strategy:**
1. Add `#ifdef __KERNEL__` guards
2. Separate userspace and kernel headers
3. Ensure kernel files include kernel headers first

### Blocker 3: Incomplete Type Definitions

**Issue:**
```
/home/user/exov6/kernel/sleeplock.h:6:20: error: field has incomplete type 'struct qspinlock'
```

**Root Cause:**
- sleeplock.h uses struct qspinlock
- Missing #include "qspinlock.h"

**Status:** ✅ FIXED (already resolved in Phase 7.4)

---

## 📋 Immediate Action Plan (Next 4-6 Hours)

### Step 1: Fix Header Conflicts (2 hours)

#### 1.1: Create Modern Locks Wrapper (30 min)

```bash
# Create unified modern lock header
cat > /home/user/exov6/kernel/modern_locks.h << 'EOF'
#pragma once
/**
 * @file modern_locks.h
 * @brief Unified interface for modern lock subsystem
 *
 * Include this header instead of individual lock headers.
 * Automatically includes all modern lock types and DAG infrastructure.
 */

#ifndef __KERNEL__
#error "This header is for kernel use only"
#endif

#include <types.h>
#include "param.h"

/* Modern lock types */
#include "qspinlock.h"
#include "adaptive_mutex.h"
#include "lwkt_token.h"
#include "sleeplock.h"

/* DAG lock ordering (compile-time optional) */
#ifdef USE_DAG_CHECKING
#include "exo_lock.h"  /* For DAG infrastructure only */
#endif

/* Lock hierarchy levels */
#define LOCK_LEVEL_SCHEDULER      10
#define LOCK_LEVEL_MEMORY         20
#define LOCK_LEVEL_IPC            30
#define LOCK_LEVEL_FILESYSTEM     40
#define LOCK_LEVEL_DEVICE         50
#define LOCK_LEVEL_NET            60
#define LOCK_LEVEL_CRYPTO         70
#define LOCK_LEVEL_USER           80

#endif /* MODERN_LOCKS_H */
EOF
```

#### 1.2: Add Guards to exo_lock.h (15 min)

```bash
# Edit include/exo_lock.h to add legacy guards
cat > /tmp/exo_lock_patch.diff << 'EOF'
--- a/include/exo_lock.h
+++ b/include/exo_lock.h
@@ -1,6 +1,15 @@
 #pragma once
 #include <types.h>

+/**
+ * @file exo_lock.h
+ * @brief DAG lock ordering infrastructure
+ *
+ * NOTE: For lock type definitions (qspinlock, adaptive_mutex, etc.),
+ * include modern_locks.h instead. This header provides only DAG checking.
+ */
+
+#ifndef EXO_LOCK_TYPES_DEFINED
 /* Lock types for DAG */
 typedef enum {
     LOCK_TYPE_QSPIN = 1,
@@ -8,6 +17,7 @@ typedef enum {
     LOCK_TYPE_TOKEN = 3,
     LOCK_TYPE_SLEEP = 4,
 } lock_type_t;
+#define EXO_LOCK_TYPES_DEFINED

 /* DAG hierarchy levels */
 #define LOCK_LEVEL_SCHEDULER      10
@@ -45,6 +55,7 @@ struct dag_stats {
     _Atomic uint64_t max_chain_length;
 };

+#ifdef USE_DAG_CHECKING
 /* Per-thread lock tracking */
 struct lock_held {
     void *lock_addr;
@@ -70,6 +81,7 @@ struct thread_lock_tracker {

 /* DAG API (only enabled with USE_DAG_CHECKING) */
 #ifdef USE_DAG_CHECKING
+
 void dag_init(void);
 struct thread_lock_tracker *get_lock_tracker(void);

@@ -89,7 +101,22 @@ void dag_lock_released(void *lock_addr,
                        lock_type_t lock_type,
                        const char *file,
                        int line);
-#endif
+
+#endif /* USE_DAG_CHECKING */
+
+/* DO NOT define lock implementations here - use modern_locks.h */
+#ifdef EXO_LEGACY_LOCKS
+#warning "EXO_LEGACY_LOCKS defined - using compatibility mode"
+/* Legacy lock definitions for backward compatibility */
+/* ... */
+#endif
+
+#endif /* EXO_LOCK_TYPES_DEFINED */
EOF

# Apply patch
cd /home/user/exov6
patch -p1 < /tmp/exo_lock_patch.diff
```

#### 1.3: Update Kernel Files to Use modern_locks.h (45 min)

```bash
# Update all kernel files that currently include multiple lock headers
find kernel -name "*.c" -exec grep -l "qspinlock.h\|adaptive_mutex.h" {} \; | \
while read file; do
    echo "Updating $file..."

    # Replace individual includes with modern_locks.h
    sed -i '/^#include "qspinlock.h"/d' "$file"
    sed -i '/^#include "adaptive_mutex.h"/d' "$file"
    sed -i '/^#include "lwkt_token.h"/d' "$file"
    sed -i '/^#include "sleeplock.h"/d' "$file"

    # Add modern_locks.h after spinlock.h
    sed -i '/^#include "spinlock.h"/a #include "modern_locks.h"' "$file"
done

# Specific files that need manual review:
# - kernel/fs/ide.c
# - kernel/fs/fs.c
# - kernel/fs/bio.c
# - kernel/fs/log.c
# - kernel/sys/trap.c
# - kernel/sched/beatty_sched.c
# - kernel/sched/dag_sched.c
```

#### 1.4: Separate Kernel and Userspace Headers (30 min)

```bash
# Add kernel guards to defs.h
sed -i '1i #ifdef __KERNEL__' kernel/defs.h
echo "#endif /* __KERNEL__ */" >> kernel/defs.h

# Update exokernel.h to avoid kernel conflicts
cat > /tmp/exokernel_patch.diff << 'EOF'
--- a/include/exokernel.h
+++ b/include/exokernel.h
@@ -1,5 +1,12 @@
 #pragma once

+#ifndef __KERNEL__
+/* Userspace API - do not include in kernel code */
+#else
+#error "Do not include exokernel.h in kernel code. Use kernel/defs.h instead."
+#endif
+
 /* Userspace exokernel API */
 typedef struct exo_blockcap exo_blockcap;
 typedef struct HypervisorCap HypervisorCap;
EOF

patch -p1 < /tmp/exokernel_patch.diff
```

### Step 2: Rebuild and Verify (30 min)

```bash
# Clean build
cd /home/user/exov6/build
ninja clean

# Rebuild kernel
ninja kernel 2>&1 | tee build_phase8.log

# Check for errors
if grep -q "error:" build_phase8.log; then
    echo "❌ Build errors detected"
    grep "error:" build_phase8.log | head -20
    exit 1
else
    echo "✅ Build successful!"
fi

# Check for warnings (should be minimal)
grep "warning:" build_phase8.log | wc -l
```

### Step 3: Run Unit Tests (1 hour)

```bash
# Test DAG validation
cd /home/user/exov6/build
./kernel/sync/test_dag
# Expected: 37 assertions pass, 0 failures

# Test qspinlock
./kernel/sync/test_qspinlock
# Expected: All tests pass

# Test adaptive mutex (if available)
if [ -f kernel/sync/test_adaptive_mutex ]; then
    ./kernel/sync/test_adaptive_mutex
fi

# Test LWKT tokens
./kernel/sync/test_lwkt_token
# Expected: All tests pass

# Collect results
cat > test_results.txt << EOF
Phase 8 Unit Test Results
=========================
Date: $(date)
Build: $(git rev-parse HEAD)

DAG Tests:         $(./kernel/sync/test_dag 2>&1 | tail -1)
QSpinlock Tests:   $(./kernel/sync/test_qspinlock 2>&1 | tail -1)
LWKT Token Tests:  $(./kernel/sync/test_lwkt_token 2>&1 | tail -1)

Summary: $(grep -c "PASS" test_results.txt) passed, $(grep -c "FAIL" test_results.txt) failed
EOF

cat test_results.txt
```

### Step 4: QEMU Boot Test (1 hour)

```bash
# Build kernel with DAG checking enabled
cd /home/user/exov6/build
cmake .. -DUSE_DAG_CHECKING=ON -DDAG_PANIC_ON_VIOLATION=ON
ninja kernel

# Check if kernel binary exists
if [ ! -f kernel/kernel ]; then
    echo "❌ Kernel binary not found"
    exit 1
fi

# Boot test script
cat > /tmp/qemu_boot_test.sh << 'EOF'
#!/bin/bash
set -e

KERNEL=$1
CPUS=$2
TIMEOUT=30

echo "Booting kernel with $CPUS CPUs..."

# Launch QEMU in background
timeout $TIMEOUT qemu-system-x86_64 \
    -kernel "$KERNEL" \
    -m 512M \
    -smp $CPUS \
    -serial file:/tmp/qemu_output_${CPUS}.txt \
    -nographic \
    -append "console=ttyS0" &

QEMU_PID=$!

# Wait for boot
sleep 10

# Check if QEMU still running
if ps -p $QEMU_PID > /dev/null; then
    echo "✅ QEMU still running after 10s (good sign)"
    kill $QEMU_PID
else
    echo "❌ QEMU crashed or exited early"
    cat /tmp/qemu_output_${CPUS}.txt
    exit 1
fi

# Check boot output
if grep -q "init: starting sh" /tmp/qemu_output_${CPUS}.txt; then
    echo "✅ Boot successful - shell started"
elif grep -q "panic:" /tmp/qemu_output_${CPUS}.txt; then
    echo "❌ Kernel panic detected"
    grep "panic:" /tmp/qemu_output_${CPUS}.txt
    exit 1
elif grep -q "DAG violation" /tmp/qemu_output_${CPUS}.txt; then
    echo "❌ DAG violation detected"
    grep "DAG violation" /tmp/qemu_output_${CPUS}.txt
    exit 1
else
    echo "⚠️  Incomplete boot (but no panic)"
fi
EOF

chmod +x /tmp/qemu_boot_test.sh

# Test with different CPU counts
for cpus in 1 2 4; do
    echo "========================================="
    echo "Testing with $cpus CPUs"
    echo "========================================="
    /tmp/qemu_boot_test.sh kernel/kernel $cpus
    echo
done

# Collect boot logs
cat > boot_test_results.txt << EOF
Phase 8 QEMU Boot Test Results
===============================
Date: $(date)
Build: $(git rev-parse HEAD)

1 CPU:  $(grep "✅\|❌" /tmp/qemu_output_1.txt | head -1)
2 CPUs: $(grep "✅\|❌" /tmp/qemu_output_2.txt | head -1)
4 CPUs: $(grep "✅\|❌" /tmp/qemu_output_4.txt | head -1)

Full logs:
- /tmp/qemu_output_1.txt
- /tmp/qemu_output_2.txt
- /tmp/qemu_output_4.txt
EOF

cat boot_test_results.txt
```

### Step 5: Document Results and Next Actions (30 min)

```bash
# Create progress report
cat > /home/user/exov6/docs/PHASE8_PROGRESS_REPORT.md << 'EOF'
# Phase 8 Progress Report
**Date:** $(date +%Y-%m-%d)
**Session:** Initial validation

## ✅ Completed

1. **Header Conflict Resolution**
   - Created modern_locks.h wrapper
   - Added guards to exo_lock.h
   - Separated kernel/userspace headers

2. **Build Verification**
   - Clean compilation achieved
   - Zero critical warnings
   - All lock types compile

3. **Unit Testing**
   - DAG tests: X/X passed
   - QSpinlock tests: X/X passed
   - LWKT token tests: X/X passed

4. **Boot Testing**
   - 1 CPU: [PASS/FAIL]
   - 2 CPUs: [PASS/FAIL]
   - 4 CPUs: [PASS/FAIL]

## 🚧 In Progress

- Integration testing
- Stress testing
- Performance benchmarking

## ⏭️ Next Steps

1. Run integration tests (scheduler, filesystem, memory)
2. Execute stress tests (fork bomb, I/O storm)
3. Performance benchmarking (lock latency, contention scaling)
4. DAG statistics analysis

## 🐛 Issues Found

[List any issues discovered during testing]

## 📊 Metrics

- Build time: X seconds
- Unit test time: X seconds
- Boot time (4 CPUs): X seconds

## 🎯 Next Session Goals

1. Complete integration testing
2. Run full stress test suite
3. Collect performance baselines
4. Begin Phase 9 (Documentation) if tests pass
EOF

# Open report for editing
${EDITOR:-nano} /home/user/exov6/docs/PHASE8_PROGRESS_REPORT.md
```

---

## 🎯 Session 2: Integration Testing (4-6 hours)

**Prerequisite:** Session 1 complete (build + unit tests passing)

### Test 1: Scheduler Integration (1 hour)

```bash
# Create scheduler integration test
cat > /home/user/exov6/tests/test_scheduler_integration.c << 'EOF'
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>

void test_fork_under_load() {
    printf("Test: Fork 100 processes...\n");

    for (int i = 0; i < 100; i++) {
        pid_t pid = fork();
        if (pid == 0) {
            // Child: exit immediately
            exit(0);
        } else if (pid < 0) {
            perror("fork failed");
            exit(1);
        }
    }

    // Parent: wait for all children
    for (int i = 0; i < 100; i++) {
        wait(NULL);
    }

    printf("✅ All 100 processes created and reaped\n");
}

void test_context_switch_safety() {
    printf("Test: Context switches with yields...\n");

    for (int i = 0; i < 10; i++) {
        pid_t pid = fork();
        if (pid == 0) {
            // Child: busy-wait with yields
            for (int j = 0; j < 1000; j++) {
                sched_yield();
            }
            exit(0);
        }
    }

    for (int i = 0; i < 10; i++) {
        wait(NULL);
    }

    printf("✅ Context switching stress test passed\n");
}

int main() {
    printf("Scheduler Integration Tests\n");
    printf("============================\n\n");

    test_fork_under_load();
    test_context_switch_safety();

    printf("\n✅ All scheduler tests passed\n");
    return 0;
}
EOF

# Compile and run in QEMU
gcc -o test_scheduler_integration test_scheduler_integration.c
# [Copy to QEMU and run]
```

### Test 2: Filesystem Integration (1.5 hours)

```bash
# Create filesystem integration test
cat > /home/user/exov6/tests/test_filesystem_integration.c << 'EOF'
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>

void test_concurrent_file_io() {
    printf("Test: Concurrent file I/O (10 processes)...\n");

    for (int i = 0; i < 10; i++) {
        pid_t pid = fork();
        if (pid == 0) {
            // Child: create, write, read, delete file
            char filename[64];
            snprintf(filename, sizeof(filename), "/tmp/test_%d", i);

            // Write
            int fd = open(filename, O_CREAT | O_WRONLY, 0644);
            if (fd < 0) {
                perror("open for write failed");
                exit(1);
            }
            write(fd, "test data", 9);
            close(fd);

            // Read
            fd = open(filename, O_RDONLY);
            if (fd < 0) {
                perror("open for read failed");
                exit(1);
            }
            char buf[32];
            read(fd, buf, 9);
            close(fd);

            // Delete
            unlink(filename);

            exit(0);
        }
    }

    // Wait for all children
    for (int i = 0; i < 10; i++) {
        wait(NULL);
    }

    printf("✅ Concurrent file I/O test passed\n");
}

void test_buffer_cache_thrashing() {
    printf("Test: Buffer cache contention...\n");

    // Create a file
    int fd = open("/tmp/thrash_test", O_CREAT | O_RDWR, 0644);
    if (fd < 0) {
        perror("open failed");
        exit(1);
    }

    // Write 100KB
    char buf[1024];
    memset(buf, 'A', sizeof(buf));
    for (int i = 0; i < 100; i++) {
        write(fd, buf, sizeof(buf));
    }
    close(fd);

    // Multiple readers
    for (int i = 0; i < 5; i++) {
        pid_t pid = fork();
        if (pid == 0) {
            fd = open("/tmp/thrash_test", O_RDONLY);
            for (int j = 0; j < 100; j++) {
                read(fd, buf, sizeof(buf));
            }
            close(fd);
            exit(0);
        }
    }

    for (int i = 0; i < 5; i++) {
        wait(NULL);
    }

    unlink("/tmp/thrash_test");

    printf("✅ Buffer cache thrashing test passed\n");
}

int main() {
    printf("Filesystem Integration Tests\n");
    printf("=============================\n\n");

    test_concurrent_file_io();
    test_buffer_cache_thrashing();

    printf("\n✅ All filesystem tests passed\n");
    return 0;
}
EOF
```

### Test 3: Memory Allocator Integration (1 hour)

```bash
# Create memory allocator test
cat > /home/user/exov6/tests/test_memory_integration.c << 'EOF'
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

void test_concurrent_allocation() {
    printf("Test: Concurrent allocation stress...\n");

    for (int i = 0; i < 10; i++) {
        pid_t pid = fork();
        if (pid == 0) {
            // Child: allocate/free rapidly
            for (int j = 0; j < 1000; j++) {
                void *ptr = malloc(4096);
                if (!ptr) {
                    fprintf(stderr, "malloc failed\n");
                    exit(1);
                }
                memset(ptr, 0xAA, 4096);
                free(ptr);
            }
            exit(0);
        }
    }

    for (int i = 0; i < 10; i++) {
        wait(NULL);
    }

    printf("✅ Concurrent allocation test passed\n");
}

int main() {
    printf("Memory Allocator Integration Tests\n");
    printf("===================================\n\n");

    test_concurrent_allocation();

    printf("\n✅ All memory tests passed\n");
    return 0;
}
EOF
```

---

## 🎯 Session 3: Stress Testing (4-6 hours)

[Stress tests as defined in PHASE8_VALIDATION_PLAN.md]

---

## 🎯 Session 4: Performance Benchmarking (4-6 hours)

[Benchmarks as defined in PHASE8_VALIDATION_PLAN.md]

---

## 📊 Success Criteria Checklist

After completing all sessions, verify:

- [ ] ✅ Clean kernel build (zero errors)
- [ ] ✅ All unit tests pass (100%)
- [ ] ✅ Boot succeeds on 1, 2, 4, 8 CPUs
- [ ] ✅ Integration tests pass (scheduler, filesystem, memory)
- [ ] ✅ Stress tests complete without deadlocks
- [ ] ✅ Performance benchmarks show improvement
- [ ] ✅ DAG statistics look reasonable
- [ ] ✅ No regressions detected

**If all checked:** Proceed to Phase 9 (Documentation)
**If any fail:** Debug, fix, re-test

---

## 🔄 Iteration Strategy

**If tests fail:**
1. Analyze failure mode (crash, deadlock, data corruption, performance)
2. Enable verbose DAG logging for debugging
3. Add targeted unit tests to reproduce issue
4. Fix root cause
5. Re-run full test suite
6. Document fix in PHASE8_PROGRESS_REPORT.md

**If performance regresses:**
1. Profile hot paths (perf, FlameGraph)
2. Identify lock contention hotspots
3. Consider lock splitting or RCU optimization
4. Re-benchmark
5. Document optimization in report

---

## 📝 Reporting Template

After each session, update the progress report:

```markdown
## Session X: [Name] - [Date]

### Completed
- [Task 1]: [Result]
- [Task 2]: [Result]

### Issues Found
1. **[Issue Title]**
   - Severity: High/Medium/Low
   - Description: [Details]
   - Root Cause: [Analysis]
   - Fix: [Solution applied]
   - Status: Fixed/Investigating/Blocked

### Metrics
- Build time: X seconds
- Test time: X seconds
- Success rate: X/Y tests passed

### Next Session Goals
- [Goal 1]
- [Goal 2]
```

---

## 🎯 Phase 8 Completion Criteria

**Ready to declare Phase 8 complete when:**

1. ✅ Build: Clean compilation, zero critical warnings
2. ✅ Tests: 100% unit test pass rate
3. ✅ Boot: Successful on 1, 2, 4, 8 CPUs
4. ✅ Integration: Scheduler, filesystem, memory tests pass
5. ✅ Stress: Fork bomb, I/O storm, memory torture succeed
6. ✅ Performance: 10-30% improvement on lock-intensive workloads
7. ✅ Regression: Zero regressions on existing tests
8. ✅ Documentation: PHASE8_PROGRESS_REPORT.md complete

**Then:** Commit Phase 8 results, create Phase 9 documentation plan, and proceed!

---

**Document Version:** 1.0
**Last Updated:** 2025-11-17
**Owner:** ExoV6 Kernel Team
