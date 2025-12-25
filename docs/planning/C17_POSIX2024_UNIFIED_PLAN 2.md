# C17 + POSIX-2024 Unified Implementation Plan

## 🎯 Core Principle: Pure C17 for Everything

**ALL code in this project MUST be written in pure C17. No legacy C, minimal assembly.**

## 📋 Granular TODO List - C17 Modernization + POSIX-2024

### Phase 1: C17 Foundation & Core Libraries

#### 1.1 C17 Language Features Implementation
- [ ] Replace all `uint`/`int` with `<stdint.h>` types (`uint32_t`, `int64_t`)
- [ ] Convert all structs to use designated initializers
- [ ] Implement `_Static_assert` for all compile-time invariants
- [ ] Use `_Alignas(64)` for cache-line aligned structures
- [ ] Implement `_Thread_local` storage for per-CPU/thread data
- [ ] Use `<stdatomic.h>` for all lock-free operations
- [ ] Convert to `<stdbool.h>` and `bool` type everywhere
- [ ] Use compound literals for all temporary structures
- [ ] Implement `_Generic` macros for type-safe interfaces
- [ ] Use `restrict` pointers for optimization hints

#### 1.2 C17 Standard Library Core (`<stddef.h>`, `<stdint.h>`, `<stdbool.h>`)
- [ ] Implement `max_align_t` properly for all architectures
- [ ] Define all exact-width integer types
- [ ] Implement `ptrdiff_t`, `size_t`, `wchar_t`
- [ ] Create `NULL` as `((void*)0)` 
- [ ] Implement `offsetof` macro using C17 semantics

#### 1.3 C17 String Library (`<string.h>`) - Pure C17
```c
// Modern C17 implementation with restrict and optimizations
void *memcpy(void * restrict dest, const void * restrict src, size_t n);
void *memmove(void *dest, const void *src, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
void *memset(void *s, int c, size_t n);
void *memchr(const void *s, int c, size_t n);

// String functions with C17 safety
char *strcpy(char * restrict dest, const char * restrict src);
char *strncpy(char * restrict dest, const char * restrict src, size_t n);
size_t strlen(const char *s);
size_t strnlen(const char *s, size_t maxlen);
```

#### 1.4 C17 Memory Allocation (`<stdlib.h>`) - Modern Algorithms
```c
// C17 aligned allocation support
void *malloc(size_t size);
void *calloc(size_t nmemb, size_t size);
void *realloc(void *ptr, size_t size);
void *aligned_alloc(size_t alignment, size_t size);  // C17 required
void free(void *ptr);

// C17 quick exit support
_Noreturn void exit(int status);
_Noreturn void _Exit(int status);
_Noreturn void quick_exit(int status);  // C17 feature
_Noreturn void abort(void);
```

#### 1.5 C17 Atomics (`<stdatomic.h>`) - Lock-free Programming
```c
// Full C17 atomic support
_Atomic(int) atomic_counter;
atomic_int lock_state;
atomic_flag spinlock = ATOMIC_FLAG_INIT;

// Memory ordering
atomic_store_explicit(&var, value, memory_order_release);
atomic_load_explicit(&var, memory_order_acquire);
atomic_compare_exchange_weak(&var, &expected, desired);
```

#### 1.6 C17 Threads (`<threads.h>`) - Native Threading
```c
// C17 threading (base for POSIX pthreads)
int thrd_create(thrd_t *thr, thrd_start_t func, void *arg);
int thrd_join(thrd_t thr, int *res);
_Noreturn void thrd_exit(int res);
thrd_t thrd_current(void);

// C17 mutexes
int mtx_init(mtx_t *mtx, int type);
int mtx_lock(mtx_t *mtx);
int mtx_timedlock(mtx_t *restrict mtx, const struct timespec *restrict ts);
int mtx_unlock(mtx_t *mtx);
```

### Phase 2: Convert Existing Code to Pure C17

#### 2.1 Kernel Modernization to C17
- [ ] Convert `kernel/boot/main.c` to pure C17 (remove assembly inline)
- [ ] Rewrite `kernel/mem/kalloc.c` with C17 atomics
- [ ] Update `kernel/sync/spinlock.c` to use `<stdatomic.h>`
- [ ] Convert `kernel/sched/proc.c` to C17 with `_Thread_local`
- [ ] Modernize `kernel/fs/fs.c` with designated initializers
- [ ] Replace all `uint` with `uint32_t` in kernel headers
- [ ] Convert inline assembly to C17 intrinsics where possible

#### 2.2 Assembly Minimization
- [ ] Convert `kernel/boot/bootasm.S` critical parts to C17
- [ ] Replace `kernel/swtch.S` with C17 context switch
- [ ] Convert `kernel/trapasm.S` trap handlers to C17
- [ ] Minimize `kernel/initcode.S` to absolute minimum
- [ ] Create C17 alternatives for all assembly macros

#### 2.3 LibOS C17 Conversion
- [ ] Convert `libos/pthread/` to build on C17 `<threads.h>`
- [ ] Modernize `libos/signal/` with C17 atomics
- [ ] Update `libos/fs/` to use C17 features
- [ ] Convert `libos/mem/memory.c` to C17 aligned allocation

### Phase 3: POSIX-2024 Implementation in Pure C17

#### 3.1 POSIX I/O in C17 (`<unistd.h>`)
```c
// File descriptors with C17 types
ssize_t read(int fd, void *buf, size_t count);
ssize_t write(int fd, const void *buf, size_t count);
int open(const char *pathname, int flags, ...);
int close(int fd);
off_t lseek(int fd, off_t offset, int whence);

// Process management in C17
pid_t fork(void);  // Implement with C17 atomics for PID generation
int execve(const char *pathname, char *const argv[], char *const envp[]);
```

#### 3.2 POSIX Threads Built on C17 (`<pthread.h>`)
```c
// Layer over C17 threads.h
typedef struct {
    thrd_t c17_thread;
    _Atomic(int) state;
    _Alignas(64) char padding[56];
} pthread_t;

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg);
```

#### 3.3 POSIX Signals with C17 Atomics (`<signal.h>`)
```c
// Signal handling with C17 atomics
typedef _Atomic(sigset_t) atomic_sigset_t;
_Thread_local sigset_t thread_sigmask;

int sigaction(int signum, const struct sigaction *act,
              struct sigaction *oldact);
```

### Phase 4: UNIX Historical Layers in C17

#### 4.1 UNIX V6/V7 Compatibility - C17 Implementation
```c
// Classic UNIX calls implemented in modern C17
int creat(const char *pathname, mode_t mode) {
    return open(pathname, O_CREAT|O_WRONLY|O_TRUNC, mode);
}

// Use C17 features for safety
int link(const char * restrict oldpath, const char * restrict newpath);
```

#### 4.2 UNIX V8-V10 STREAMS - C17 Implementation
```c
// STREAMS in pure C17
typedef struct strbuf {
    int32_t maxlen;
    int32_t len;
    char *buf;
} strbuf_t;

// Modern C17 STREAMS operations
int getmsg(int fd, strbuf_t * restrict ctlptr, 
           strbuf_t * restrict dataptr, int32_t * restrict flagsp);
```

#### 4.3 SVR4.2 Features - C17 Implementation
```c
// Dynamic linking with C17
void *dlopen(const char * restrict filename, int flags);
void *dlsym(void * restrict handle, const char * restrict symbol);

// Real-time with C17 time support
int clock_gettime(clockid_t clk_id, struct timespec *tp);
```

#### 4.4 BSD Sockets - C17 Implementation
```c
// Sockets with C17 types and atomics
int socket(int domain, int type, int protocol);
ssize_t send(int sockfd, const void *buf, size_t len, int flags);

// Use C17 atomics for socket state
typedef struct {
    _Atomic(int) state;
    _Atomic(int) refcount;
    _Alignas(64) uint8_t buffer[SOCK_BUFFER_SIZE];
} socket_t;
```

### Phase 5: Hardware Abstraction Layer (HAL) in Pure C17

#### 5.1 C17 HAL Architecture
```c
// include/hal/cpu.h - Pure C17
typedef struct {
    _Alignas(64) _Atomic(uint64_t) flags;
    _Thread_local void *current_task;
    uint64_t (*read_timestamp)(void);
    void (*enable_interrupts)(void);
    void (*disable_interrupts)(void);
} cpu_ops_t;

// Platform selection at compile time
#if defined(__x86_64__)
    extern const cpu_ops_t x86_64_cpu_ops;
    #define CPU_OPS x86_64_cpu_ops
#elif defined(__aarch64__)
    extern const cpu_ops_t aarch64_cpu_ops;
    #define CPU_OPS aarch64_cpu_ops
#endif
```

#### 5.2 Memory HAL in C17
```c
// include/hal/memory.h - Pure C17
typedef struct {
    void *(*map_page)(uintptr_t phys, uintptr_t virt, uint32_t flags);
    void (*unmap_page)(uintptr_t virt);
    void (*flush_tlb)(void);
    _Atomic(uint64_t) *(*get_pte)(uintptr_t virt);
} memory_ops_t;
```

### Phase 6: Build System for Pure C17

#### 6.1 CMake C17 Enforcement
```cmake
# Enforce C17 standard strictly
set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)  # No GNU extensions

# C17 compiler flags
set(C17_FLAGS "-std=c17 -Wall -Wextra -Wpedantic")
set(C17_FLAGS "${C17_FLAGS} -Wvla")  # No VLAs
set(C17_FLAGS "${C17_FLAGS} -D_POSIX_C_SOURCE=202405L")  # POSIX-2024

# Detect C17 features
include(CheckCSourceCompiles)
check_c_source_compiles("
    #include <stdatomic.h>
    int main() { _Atomic(int) x = 0; return 0; }
" HAS_C17_ATOMICS)

check_c_source_compiles("
    #include <threads.h>
    int main() { thrd_t t; return 0; }
" HAS_C17_THREADS)

if(NOT HAS_C17_ATOMICS OR NOT HAS_C17_THREADS)
    message(FATAL_ERROR "C17 support required")
endif()
```

### Phase 7: Testing & Validation in C17

#### 7.1 C17 Unit Testing Framework
```c
// tests/c17_test.h - Pure C17 testing
#include <stdbool.h>
#include <stdint.h>

_Static_assert(sizeof(void*) == 8, "64-bit required");

#define TEST_ASSERT(cond) \
    _Static_assert(_Generic((cond), bool: 1, default: 0), \
                   "condition must be bool")

typedef struct {
    const char *name;
    bool (*test_func)(void);
    _Atomic(bool) passed;
} test_case_t;
```

#### 7.2 POSIX Compliance Tests in C17
```c
// tests/posix_compliance.c
#include <unistd.h>
#include <stdatomic.h>

bool test_fork_c17(void) {
    _Atomic(pid_t) child_pid = fork();
    if (atomic_load(&child_pid) == 0) {
        // Child process
        _Exit(0);
    }
    return atomic_load(&child_pid) > 0;
}
```

## 📊 C17 Modernization Metrics

```
C17 Conversion Progress:
├── Kernel files: 0/248 converted to C17
├── LibOS files: 0/67 converted to C17
├── User programs: 0/227 converted to C17
├── Headers: 0/100 using C17 features
├── Assembly files: 13 files to minimize/convert
└── Build system: CMake C17 enforcement pending

C17 Feature Adoption:
├── stdint.h types: 15% adopted
├── stdatomic.h: 0% implemented
├── threads.h: 0% implemented
├── _Static_assert: 5% coverage
├── _Alignas: 2% usage
├── Designated init: 10% usage
├── Compound literals: 1% usage
└── restrict pointers: 0% usage
```

## 🎯 Success Criteria for C17-POSIX-2024

1. **100% Pure C17 Code**
   - Zero legacy C constructs
   - Maximum 1% assembly (boot only)
   - All modern C17 features utilized

2. **Complete POSIX-2024 Compliance**
   - All 1500+ functions in C17
   - Full test suite passing
   - Certification ready

3. **Performance with C17**
   - Compiler optimizations enabled by restrict
   - Lock-free atomics throughout
   - Cache-aligned structures

4. **Maintainability**
   - Type-safe with C17 features
   - Static assertions for invariants
   - Modern, readable code

## 🚀 Immediate Actions (This Week)

1. **Set up C17 build enforcement**
   ```bash
   # Update CMakeLists.txt with strict C17
   cmake -DCMAKE_C_STANDARD=17 -DCMAKE_C_EXTENSIONS=OFF ..
   ```

2. **Create C17 standard headers**
   ```bash
   # Create modern headers
   touch include/{stdatomic.h,threads.h,stdalign.h}
   ```

3. **Start kernel C17 conversion**
   - Begin with `kernel/mem/kalloc.c`
   - Convert to stdint.h types
   - Add static assertions

4. **Implement first C17 libc functions**
   - Start with `memcpy` using restrict
   - Implement `aligned_alloc`
   - Create atomic reference counting

5. **Build C17 test framework**
   - Unit tests with static assertions
   - Type-generic test macros
   - Atomic test counters

## 📝 Development Rules

1. **NEVER use legacy C types** (uint, ulong, etc.)
2. **ALWAYS use C17 features** when applicable
3. **MINIMIZE assembly** - convert to C17 intrinsics
4. **ENFORCE type safety** with _Generic and static assertions
5. **USE modern algorithms** (lock-free, cache-aware)
6. **DOCUMENT C17 choices** in code comments

---

**This is the definitive plan: Pure C17 implementation of complete POSIX-2024 with historical UNIX compatibility.**