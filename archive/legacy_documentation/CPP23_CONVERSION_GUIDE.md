# C++23 Conversion Guidelines for FeuerBird

## Overview
This guide provides patterns and best practices for converting FeuerBird from C17 to C++23 while maintaining POSIX compliance and exokernel architecture.

## Core Principles

1. **Gradual Migration**: Files can be migrated individually
2. **C Compatibility**: Maintain C interfaces where needed
3. **No Exceptions/RTTI**: Kernel constraints apply everywhere
4. **Zero-Cost Abstractions**: C++ features must not add overhead
5. **Type Safety**: Leverage C++23 type system fully

## Conversion Patterns

### 1. File Structure Conversion

#### C17 Original
```c
// file: kernel/cap.c
#include "types.h"
#include "defs.h"
#include "cap.h"

struct capability {
    uint32_t id;
    uint32_t type;
    void* resource;
};

int cap_create(uint32_t type, void* resource) {
    // Implementation
    return 0;  // success
}
```

#### C++23 Converted
```cpp
// file: kernel/capability.cpp
module;
#include <cstdint>
#include <expected>
#include <span>

export module exo.capability;

import exo.types;
import exo.memory;

export namespace exo {

enum class CapabilityType : std::uint32_t {
    Memory = 0,
    CPU = 1,
    Disk = 2,
    Network = 3,
    IPC = 4,
    Zone = 5
};

class Capability {
private:
    std::uint32_t id_;
    CapabilityType type_;
    void* resource_;
    
public:
    constexpr Capability(CapabilityType type, void* resource)
        : id_(generate_id()), type_(type), resource_(resource) {}
    
    [[nodiscard]] auto type() const noexcept -> CapabilityType { 
        return type_; 
    }
    
    [[nodiscard]] auto resource() const noexcept -> void* { 
        return resource_; 
    }
    
private:
    static auto generate_id() -> std::uint32_t;
};

[[nodiscard]] auto create_capability(CapabilityType type, void* resource) 
    -> std::expected<Capability, ErrorCode> {
    if (!validate_resource(type, resource)) {
        return std::unexpected(ErrorCode::InvalidResource);
    }
    return Capability{type, resource};
}

} // namespace exo
```

### 2. Error Handling Migration

#### C17 Pattern (errno)
```c
int open_file(const char* path, int flags) {
    if (!path) {
        errno = EINVAL;
        return -1;
    }
    
    int fd = do_open(path, flags);
    if (fd < 0) {
        errno = ENOENT;
        return -1;
    }
    
    return fd;
}
```

#### C++23 Pattern (std::expected)
```cpp
[[nodiscard]] auto open_file(std::string_view path, OpenFlags flags) 
    -> std::expected<FileDescriptor, ErrorCode> {
    
    if (path.empty()) {
        return std::unexpected(ErrorCode::InvalidArgument);
    }
    
    if (auto fd = do_open(path, flags); fd) {
        return FileDescriptor{*fd};
    } else {
        return std::unexpected(ErrorCode::FileNotFound);
    }
}

// Usage
auto result = open_file("/etc/passwd", OpenFlags::ReadOnly);
if (result) {
    auto& fd = *result;
    // Use fd
} else {
    handle_error(result.error());
}
```

### 3. Buffer Management

#### C17 Pattern
```c
void process_buffer(char* buf, size_t len) {
    for (size_t i = 0; i < len; i++) {
        buf[i] = toupper(buf[i]);
    }
}
```

#### C++23 Pattern
```cpp
void process_buffer(std::span<char> buffer) {
    std::ranges::transform(buffer, buffer.begin(), 
        [](char c) { return std::toupper(c); });
}

// Or with concepts
template<std::ranges::contiguous_range R>
    requires std::same_as<std::ranges::range_value_t<R>, char>
void process_buffer(R&& buffer) {
    std::ranges::transform(buffer, std::ranges::begin(buffer),
        [](char c) { return std::toupper(c); });
}
```

### 4. Resource Management (RAII)

#### C17 Pattern
```c
int copy_file(const char* src, const char* dst) {
    int fd_src = open(src, O_RDONLY);
    if (fd_src < 0) return -1;
    
    int fd_dst = open(dst, O_WRONLY | O_CREAT);
    if (fd_dst < 0) {
        close(fd_src);
        return -1;
    }
    
    // Copy logic
    
    close(fd_dst);
    close(fd_src);
    return 0;
}
```

#### C++23 Pattern
```cpp
class FileHandle {
    int fd_ = -1;
public:
    explicit FileHandle(int fd) : fd_(fd) {}
    ~FileHandle() { if (fd_ >= 0) ::close(fd_); }
    
    FileHandle(FileHandle&& other) noexcept 
        : fd_(std::exchange(other.fd_, -1)) {}
    
    FileHandle& operator=(FileHandle&& other) noexcept {
        if (this != &other) {
            if (fd_ >= 0) ::close(fd_);
            fd_ = std::exchange(other.fd_, -1);
        }
        return *this;
    }
    
    // Delete copy operations
    FileHandle(const FileHandle&) = delete;
    FileHandle& operator=(const FileHandle&) = delete;
    
    [[nodiscard]] auto get() const noexcept -> int { return fd_; }
    explicit operator bool() const noexcept { return fd_ >= 0; }
};

[[nodiscard]] auto copy_file(std::string_view src, std::string_view dst)
    -> std::expected<void, ErrorCode> {
    
    FileHandle fd_src{::open(src.data(), O_RDONLY)};
    if (!fd_src) {
        return std::unexpected(ErrorCode::SourceNotFound);
    }
    
    FileHandle fd_dst{::open(dst.data(), O_WRONLY | O_CREAT)};
    if (!fd_dst) {
        return std::unexpected(ErrorCode::DestinationError);
    }
    
    // Copy logic - RAII ensures cleanup
    
    return {};  // Success
}
```

### 5. Type-Safe System Calls

#### C17 Pattern
```c
long syscall(long number, long arg1, long arg2, long arg3);

// Usage - error prone
int result = syscall(SYS_open, (long)path, O_RDONLY, 0);
```

#### C++23 Pattern
```cpp
template<typename... Args>
concept SyscallArgs = (std::integral<Args> || std::is_pointer_v<Args>) && ...;

template<SyscallNumber N, SyscallArgs... Args>
[[nodiscard]] auto syscall(Args... args) 
    -> std::expected<SyscallResult<N>, ErrorCode> {
    
    auto result = do_syscall(static_cast<long>(N), 
                            static_cast<long>(args)...);
    
    if (result < 0) {
        return std::unexpected(static_cast<ErrorCode>(-result));
    }
    
    return SyscallResult<N>{result};
}

// Type-safe usage
auto result = syscall<SyscallNumber::Open>(path, OpenFlags::ReadOnly);
```

### 6. Synchronization Primitives

#### C17 Pattern
```c
struct spinlock {
    volatile int locked;
};

void acquire(struct spinlock* lock) {
    while (__sync_lock_test_and_set(&lock->locked, 1)) {
        while (lock->locked) {
            __builtin_ia32_pause();
        }
    }
}

void release(struct spinlock* lock) {
    __sync_lock_release(&lock->locked);
}
```

#### C++23 Pattern
```cpp
#include <atomic>
#include <concepts>

template<typename T>
concept Lockable = requires(T& t) {
    { t.lock() } -> std::same_as<void>;
    { t.unlock() } -> std::same_as<void>;
    { t.try_lock() } -> std::same_as<bool>;
};

class SpinLock {
    std::atomic_flag flag_ = ATOMIC_FLAG_INIT;
    
public:
    void lock() noexcept {
        while (flag_.test_and_set(std::memory_order_acquire)) {
            while (flag_.test(std::memory_order_relaxed)) {
                __builtin_ia32_pause();
            }
        }
    }
    
    void unlock() noexcept {
        flag_.clear(std::memory_order_release);
    }
    
    [[nodiscard]] bool try_lock() noexcept {
        return !flag_.test_and_set(std::memory_order_acquire);
    }
};

template<Lockable Lock>
class [[nodiscard]] LockGuard {
    Lock& lock_;
public:
    explicit LockGuard(Lock& lock) : lock_(lock) { lock_.lock(); }
    ~LockGuard() { lock_.unlock(); }
    
    // Delete copy/move
    LockGuard(const LockGuard&) = delete;
    LockGuard& operator=(const LockGuard&) = delete;
};

// Usage with CTAD
SpinLock lock;
{
    LockGuard guard{lock};  // CTAD deduces type
    // Critical section
}  // Automatic unlock
```

### 7. String Handling

#### C17 Pattern
```c
char* concat_strings(const char* s1, const char* s2) {
    size_t len1 = strlen(s1);
    size_t len2 = strlen(s2);
    char* result = malloc(len1 + len2 + 1);
    if (!result) return NULL;
    
    strcpy(result, s1);
    strcat(result, s2);
    return result;
}
```

#### C++23 Pattern
```cpp
[[nodiscard]] auto concat_strings(std::string_view s1, std::string_view s2)
    -> std::expected<std::string, ErrorCode> {
    
    if (s1.size() + s2.size() > MaxStringLength) {
        return std::unexpected(ErrorCode::StringTooLong);
    }
    
    return std::format("{}{}", s1, s2);
}

// For kernel (no std::string)
template<std::size_t N>
class FixedString {
    std::array<char, N> data_{};
    std::size_t len_ = 0;
    
public:
    constexpr FixedString() = default;
    
    constexpr auto append(std::string_view sv) -> bool {
        if (len_ + sv.size() >= N) return false;
        std::copy(sv.begin(), sv.end(), data_.begin() + len_);
        len_ += sv.size();
        data_[len_] = '\0';
        return true;
    }
    
    [[nodiscard]] constexpr auto view() const noexcept -> std::string_view {
        return {data_.data(), len_};
    }
};
```

### 8. Compile-Time Validation

#### C++23 Concepts
```cpp
template<typename T>
concept Capability = requires(T t) {
    { t.id() } -> std::convertible_to<std::uint32_t>;
    { t.type() } -> std::same_as<CapabilityType>;
    { t.validate() } -> std::same_as<bool>;
};

template<typename T>
concept Process = requires(T t) {
    typename T::pid_type;
    { t.pid() } -> std::convertible_to<typename T::pid_type>;
    { t.state() } -> std::same_as<ProcessState>;
    { t.capabilities() } -> std::ranges::range;
};

template<Process P, Capability C>
auto grant_capability(P& process, C&& cap) 
    -> std::expected<void, ErrorCode> {
    
    if (!cap.validate()) {
        return std::unexpected(ErrorCode::InvalidCapability);
    }
    
    process.add_capability(std::forward<C>(cap));
    return {};
}
```

### 9. C Interface Compatibility

#### Maintaining C ABI
```cpp
// kernel/syscall_interface.hpp
extern "C" {

// C-compatible interface
struct c_capability {
    uint32_t id;
    uint32_t type;
    void* resource;
};

int sys_create_capability(uint32_t type, void* resource, 
                          struct c_capability* out);
int sys_destroy_capability(uint32_t id);

}  // extern "C"

// C++ implementation
namespace exo {

[[nodiscard]] auto sys_create_capability_impl(uint32_t type, void* resource)
    -> std::expected<Capability, ErrorCode> {
    // C++ implementation
}

}  // namespace exo

// C wrapper implementation
extern "C" int sys_create_capability(uint32_t type, void* resource,
                                     struct c_capability* out) {
    auto result = exo::sys_create_capability_impl(type, resource);
    if (!result) {
        return -static_cast<int>(result.error());
    }
    
    // Convert to C struct
    out->id = result->id();
    out->type = static_cast<uint32_t>(result->type());
    out->resource = result->resource();
    return 0;
}
```

## Zone-Specific Guidelines

### Kernel Zone
- Use freestanding C++23
- No dynamic allocation (use static pools)
- No exceptions or RTTI
- Minimal template instantiation
- Direct hardware access patterns

### LibOS Zone  
- Full C++23 with libc++
- Can use std::pmr allocators
- Thread-local storage available
- Full standard library (minus exceptions)
- POSIX wrapper layer

### User Zone
- Full C++23 features
- Standard library algorithms
- Ranges and views
- Format library for I/O
- Coroutines for async (optional)

## Migration Checklist

### Per-File Migration Steps
- [ ] Rename .c to .cpp
- [ ] Update includes to C++ headers
- [ ] Add namespace (exo:: for kernel, libos:: for LibOS)
- [ ] Convert structs to classes where appropriate
- [ ] Replace malloc/free with RAII
- [ ] Convert error codes to std::expected
- [ ] Add [[nodiscard]] attributes
- [ ] Use concepts for templates
- [ ] Add constexpr where possible
- [ ] Update build system entry

### Testing After Migration
- [ ] Compile with -std=c++23
- [ ] Run unit tests
- [ ] Check ABI compatibility
- [ ] Verify performance (no regression)
- [ ] Test C interface if exposed
- [ ] Run static analysis
- [ ] Check binary size

## Common Pitfalls

1. **Object Slicing**: Use references/pointers for polymorphism
2. **Hidden Copies**: Mark single-arg constructors explicit
3. **ODR Violations**: Use inline for header definitions
4. **ABI Changes**: Keep C interfaces stable
5. **Template Bloat**: Use explicit instantiation

## Performance Considerations

### Zero-Cost Abstractions
```cpp
// Good: No runtime cost
template<std::size_t N>
using Buffer = std::array<char, N>;

// Bad: Runtime allocation
using Buffer = std::vector<char>;
```

### Compile-Time Computation
```cpp
// Compute at compile time
constexpr auto table = []() {
    std::array<int, 256> t{};
    for (int i = 0; i < 256; ++i) {
        t[i] = compute_value(i);
    }
    return t;
}();
```

### Link-Time Optimization
```cpp
// Enable LTO for release builds
// In CMakeLists.txt or Makefile:
// -flto=thin for Clang
// -flto for GCC
```

## Tools & Validation

### Automated Migration Tools
```bash
# Use clang-tidy for automated fixes
clang-tidy -fix -checks="modernize-*" file.cpp

# Format code
clang-format -i -style=LLVM file.cpp

# Check for C++23 features
clang++ -std=c++23 -fsyntax-only file.cpp
```

### Static Analysis
```bash
# Clang static analyzer
scan-build make

# Clang-tidy checks
clang-tidy file.cpp -checks="*" -- -std=c++23

# Address sanitizer
clang++ -fsanitize=address -std=c++23 file.cpp
```

## Success Metrics

- **Type Safety**: 100% of syscalls type-checked
- **Error Handling**: No raw error codes
- **Resource Management**: All resources RAII-managed
- **Compile Time**: < 30 seconds full rebuild
- **Binary Size**: < 10% increase from C17
- **Performance**: No measurable regression