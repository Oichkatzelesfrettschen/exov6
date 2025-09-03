#!/bin/bash
# Bootstrap script for building LLVM libc++ with C++23 support
# Specifically configured for exokernel/embedded OS development

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LLVM_VERSION="18.1.0"  # Latest stable with full C++23

echo "=== LLVM libc++ Bootstrap for FeuerBird Exokernel ==="
echo "Building standalone C++23 standard library"
echo

# Configuration options
INSTALL_PREFIX="$PROJECT_ROOT/llvm-libc++"
BUILD_DIR="$PROJECT_ROOT/llvm-build"
LLVM_SRC="$PROJECT_ROOT/llvm-project"

# Parse arguments
CLEAN_BUILD=false
DOWNLOAD_LLVM=true
while [[ $# -gt 0 ]]; do
    case $1 in
        --clean)
            CLEAN_BUILD=true
            shift
            ;;
        --no-download)
            DOWNLOAD_LLVM=false
            shift
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Clean previous builds if requested
if [ "$CLEAN_BUILD" = true ]; then
    echo "Cleaning previous builds..."
    rm -rf "$BUILD_DIR" "$INSTALL_PREFIX"
fi

# Download LLVM source if needed
if [ "$DOWNLOAD_LLVM" = true ]; then
    if [ ! -d "$LLVM_SRC" ]; then
        echo "Downloading LLVM $LLVM_VERSION source..."
        git clone --depth 1 --branch "llvmorg-$LLVM_VERSION" \
            https://github.com/llvm/llvm-project.git "$LLVM_SRC"
    else
        echo "LLVM source already exists at $LLVM_SRC"
    fi
fi

# Create build directory
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"

# Configure build for embedded/kernel use
echo
echo "Configuring LLVM libc++ build..."
echo "Options:"
echo "  - C++23 standard"
echo "  - Static libraries only"
echo "  - No exceptions (kernel-safe)"
echo "  - No RTTI (smaller binary)"
echo "  - Freestanding support"
echo

cat > cmake_config.sh << 'EOF'
#!/bin/bash
cmake -G Ninja \
    -S ../llvm-project/runtimes \
    -B . \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_INSTALL_PREFIX="../llvm-libc++" \
    -DCMAKE_C_COMPILER=clang \
    -DCMAKE_CXX_COMPILER=clang++ \
    -DCMAKE_CXX_STANDARD=23 \
    -DCMAKE_CXX_STANDARD_REQUIRED=YES \
    -DLLVM_ENABLE_RUNTIMES="libcxx;libcxxabi;libunwind" \
    -DLIBCXX_ENABLE_SHARED=OFF \
    -DLIBCXX_ENABLE_STATIC=ON \
    -DLIBCXX_ENABLE_EXCEPTIONS=OFF \
    -DLIBCXX_ENABLE_RTTI=OFF \
    -DLIBCXX_ENABLE_THREADS=ON \
    -DLIBCXX_HAS_PTHREAD_API=ON \
    -DLIBCXX_ENABLE_MONOTONIC_CLOCK=ON \
    -DLIBCXX_ENABLE_FILESYSTEM=OFF \
    -DLIBCXX_ENABLE_RANDOM_DEVICE=OFF \
    -DLIBCXX_ENABLE_LOCALIZATION=OFF \
    -DLIBCXX_ENABLE_UNICODE=OFF \
    -DLIBCXX_ENABLE_WIDE_CHARACTERS=OFF \
    -DLIBCXXABI_ENABLE_SHARED=OFF \
    -DLIBCXXABI_ENABLE_STATIC=ON \
    -DLIBCXXABI_ENABLE_EXCEPTIONS=OFF \
    -DLIBCXXABI_ENABLE_THREADS=ON \
    -DLIBCXXABI_USE_LLVM_UNWINDER=ON \
    -DLIBUNWIND_ENABLE_SHARED=OFF \
    -DLIBUNWIND_ENABLE_STATIC=ON \
    -DLIBUNWIND_ENABLE_THREADS=ON \
    -DLLVM_ENABLE_PIC=OFF \
    -DLLVM_BUILD_32_BITS=OFF
EOF

chmod +x cmake_config.sh
./cmake_config.sh

# Build libc++
echo
echo "Building libc++..."
ninja -j$(nproc)

# Install to project directory
echo
echo "Installing libc++ to $INSTALL_PREFIX..."
ninja install

# Create configuration header for kernel use
echo
echo "Creating kernel configuration headers..."

mkdir -p "$INSTALL_PREFIX/include/exo"
cat > "$INSTALL_PREFIX/include/exo/libcxx_config.h" << 'EOF'
#ifndef EXO_LIBCXX_CONFIG_H
#define EXO_LIBCXX_CONFIG_H

// Configuration for using libc++ in FeuerBird exokernel

// Freestanding environment for kernel
#ifdef KERNEL_BUILD
  #define _LIBCPP_FREESTANDING
  #define _LIBCPP_NO_EXCEPTIONS
  #define _LIBCPP_NO_RTTI
  #define _LIBCPP_HAS_NO_THREADS
  #define _LIBCPP_HAS_NO_FILESYSTEM
  #define _LIBCPP_HAS_NO_LOCALIZATION
  #define _LIBCPP_HAS_NO_RANDOM_DEVICE
#endif

// LibOS has more features available
#ifdef LIBOS_BUILD
  #define _LIBCPP_NO_EXCEPTIONS
  #define _LIBCPP_NO_RTTI
  #define _LIBCPP_HAS_THREAD_API_PTHREAD
#endif

// User space gets full features (minus exceptions/RTTI)
#ifdef USER_BUILD
  #define _LIBCPP_NO_EXCEPTIONS
  #define _LIBCPP_NO_RTTI
  #define _LIBCPP_HAS_THREAD_API_PTHREAD
#endif

// C++23 features
#define _LIBCPP_STD_VER 23

// Custom allocator hooks for kernel
#ifdef KERNEL_BUILD
namespace std {
  template<typename T>
  struct exo_allocator {
    using value_type = T;
    
    T* allocate(size_t n);
    void deallocate(T* p, size_t n);
  };
}
#endif

#endif // EXO_LIBCXX_CONFIG_H
EOF

# Create pkg-config file
mkdir -p "$INSTALL_PREFIX/lib/pkgconfig"
cat > "$INSTALL_PREFIX/lib/pkgconfig/libcxx.pc" << EOF
prefix=$INSTALL_PREFIX
exec_prefix=\${prefix}
libdir=\${exec_prefix}/lib
includedir=\${prefix}/include

Name: libc++
Description: LLVM C++ Standard Library for FeuerBird
Version: $LLVM_VERSION
Requires:
Libs: -L\${libdir} -lc++ -lc++abi -lunwind
Cflags: -I\${includedir} -I\${includedir}/c++/v1 -std=c++23 -fno-exceptions -fno-rtti
EOF

# Create usage script
cat > "$PROJECT_ROOT/use_libcxx.sh" << EOF
#!/bin/bash
# Source this script to use the custom libc++ build

export LIBCXX_ROOT="$INSTALL_PREFIX"
export CXXFLAGS="-stdlib=libc++ -I\$LIBCXX_ROOT/include/c++/v1 -std=c++23 -fno-exceptions -fno-rtti"
export LDFLAGS="-L\$LIBCXX_ROOT/lib -lc++ -lc++abi -lunwind"

# For kernel builds
export KERNEL_CXXFLAGS="\$CXXFLAGS -DKERNEL_BUILD -ffreestanding -nostdlib"

# For LibOS builds
export LIBOS_CXXFLAGS="\$CXXFLAGS -DLIBOS_BUILD"

# For user programs
export USER_CXXFLAGS="\$CXXFLAGS -DUSER_BUILD"

echo "libc++ environment configured:"
echo "  LIBCXX_ROOT: \$LIBCXX_ROOT"
echo "  C++ Standard: C++23"
echo "  Features: No exceptions, No RTTI"
EOF

chmod +x "$PROJECT_ROOT/use_libcxx.sh"

# Create test program
echo
echo "Creating test program..."

cat > "$BUILD_DIR/test_libcxx.cpp" << 'EOF'
// Test program for C++23 libc++ features
#include <expected>
#include <span>
#include <format>
#include <ranges>
#include <concepts>
#include <array>

// Test C++23 features
template<std::integral T>
constexpr T add(T a, T b) {
    return a + b;
}

// Test std::expected (C++23)
std::expected<int, const char*> divide(int a, int b) {
    if (b == 0) {
        return std::unexpected("Division by zero");
    }
    return a / b;
}

// Test std::span
void process_buffer(std::span<const int> data) {
    for (auto& val : data) {
        // Process
    }
}

int main() {
    // Test concepts
    static_assert(add(1, 2) == 3);
    
    // Test expected
    auto result = divide(10, 2);
    if (result) {
        // Success
    }
    
    // Test span
    std::array<int, 5> arr = {1, 2, 3, 4, 5};
    process_buffer(arr);
    
    return 0;
}
EOF

# Compile test program
echo "Testing C++23 compilation..."
source "$PROJECT_ROOT/use_libcxx.sh"
clang++ $USER_CXXFLAGS "$BUILD_DIR/test_libcxx.cpp" -o "$BUILD_DIR/test_libcxx" $LDFLAGS

if [ -f "$BUILD_DIR/test_libcxx" ]; then
    echo "✓ C++23 test compilation successful!"
else
    echo "✗ C++23 test compilation failed"
    exit 1
fi

# Summary
echo
echo "=== Bootstrap Complete ==="
echo
echo "libc++ installed to: $INSTALL_PREFIX"
echo "To use in your build:"
echo "  source $PROJECT_ROOT/use_libcxx.sh"
echo
echo "Next steps:"
echo "1. Update Makefile to use KERNEL_CXXFLAGS, LIBOS_CXXFLAGS, USER_CXXFLAGS"
echo "2. Update meson.build with cpp_args and cpp_link_args"
echo "3. Begin C++23 migration with kernel zone first"
echo
echo "Example Makefile usage:"
echo "  KERNEL_OBJS: \$(CXX) \$(KERNEL_CXXFLAGS) -c kernel/file.cpp"
echo "  LIBOS_OBJS:  \$(CXX) \$(LIBOS_CXXFLAGS) -c libos/file.cpp"
echo "  USER_OBJS:   \$(CXX) \$(USER_CXXFLAGS) -c user/file.cpp"