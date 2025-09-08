#!/bin/bash
# Universal build script for ExoV6
# Handles cross-compilation and native builds for x86_64 and AArch64

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Default values
ARCH=""
BUILD_TYPE="Release"
JOBS=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
CLEAN=false
VERBOSE=false

# Function to print colored output
print_status() {
    echo -e "${GREEN}[+]${NC} $1"
}

print_error() {
    echo -e "${RED}[!]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[*]${NC} $1"
}

# Function to detect host architecture
detect_host_arch() {
    local arch=$(uname -m)
    case $arch in
        x86_64)
            echo "x86_64"
            ;;
        arm64|aarch64)
            echo "aarch64"
            ;;
        *)
            print_error "Unknown host architecture: $arch"
            exit 1
            ;;
    esac
}

# Function to check for required tools
check_requirements() {
    local missing_tools=()
    
    for tool in cmake clang make; do
        if ! command -v $tool &> /dev/null; then
            missing_tools+=($tool)
        fi
    done
    
    if [ ${#missing_tools[@]} -ne 0 ]; then
        print_error "Missing required tools: ${missing_tools[*]}"
        print_status "Please install missing tools and try again"
        exit 1
    fi
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --arch)
            ARCH="$2"
            shift 2
            ;;
        --debug)
            BUILD_TYPE="Debug"
            shift
            ;;
        --clean)
            CLEAN=true
            shift
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --jobs)
            JOBS="$2"
            shift 2
            ;;
        --help)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --arch <arch>    Target architecture (x86_64, aarch64, or auto)"
            echo "  --debug          Build in debug mode"
            echo "  --clean          Clean build directory before building"
            echo "  --verbose        Enable verbose output"
            echo "  --jobs <n>       Number of parallel jobs (default: auto)"
            echo "  --help           Show this help message"
            echo ""
            echo "Examples:"
            echo "  $0                          # Auto-detect architecture"
            echo "  $0 --arch x86_64            # Cross-compile for x86_64"
            echo "  $0 --arch aarch64 --debug   # Build for ARM64 in debug mode"
            exit 0
            ;;
        *)
            print_error "Unknown option: $1"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

# Check for required tools
check_requirements

# Detect or validate architecture
HOST_ARCH=$(detect_host_arch)
if [ -z "$ARCH" ]; then
    ARCH=$HOST_ARCH
    print_status "Auto-detected architecture: $ARCH"
else
    print_status "Target architecture: $ARCH"
fi

print_status "Host architecture: $HOST_ARCH"

# Determine if we're cross-compiling
if [ "$HOST_ARCH" != "$ARCH" ]; then
    CROSS_COMPILE=true
    print_warning "Cross-compilation: $HOST_ARCH -> $ARCH"
else
    CROSS_COMPILE=false
    print_status "Native compilation for $ARCH"
fi

# Set build directory based on architecture
BUILD_DIR="build-${ARCH}"

# Clean if requested
if [ "$CLEAN" = true ]; then
    print_status "Cleaning build directory: $BUILD_DIR"
    rm -rf "$BUILD_DIR"
fi

# Create build directory
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"

# Configure CMake
print_status "Configuring CMake..."
CMAKE_ARGS=(
    -DCMAKE_BUILD_TYPE="$BUILD_TYPE"
    -DARCH="$ARCH"
)

# Add toolchain file for cross-compilation
if [ "$CROSS_COMPILE" = true ] || [ "$ARCH" != "$(uname -m)" ]; then
    TOOLCHAIN_FILE="../toolchain-${ARCH}.cmake"
    if [ -f "$TOOLCHAIN_FILE" ]; then
        CMAKE_ARGS+=(-DCMAKE_TOOLCHAIN_FILE="$TOOLCHAIN_FILE")
        print_status "Using toolchain file: $TOOLCHAIN_FILE"
    else
        print_warning "No toolchain file found for $ARCH, using default settings"
    fi
fi

# Add verbose flag if requested
if [ "$VERBOSE" = true ]; then
    CMAKE_ARGS+=(-DCMAKE_VERBOSE_MAKEFILE=ON)
fi

# Run CMake configuration
if ! cmake "${CMAKE_ARGS[@]}" ..; then
    print_error "CMake configuration failed"
    exit 1
fi

# Build the project
print_status "Building with $JOBS parallel jobs..."
if [ "$VERBOSE" = true ]; then
    cmake --build . -j"$JOBS" --verbose
else
    cmake --build . -j"$JOBS"
fi

# Check if build succeeded
if [ $? -eq 0 ]; then
    print_status "Build completed successfully!"
    
    # List generated artifacts
    echo ""
    print_status "Generated artifacts:"
    if [ -f "bin/kernel.elf" ]; then
        echo "  - Kernel: bin/kernel.elf"
        file bin/kernel.elf | sed 's/^/    /'
    fi
    if [ -f "fs.img" ]; then
        echo "  - Filesystem: fs.img"
        ls -lh fs.img | sed 's/^/    /'
    fi
    if [ -f "bin/tools/mkfs" ]; then
        echo "  - Tools: bin/tools/mkfs"
    fi
else
    print_error "Build failed"
    exit 1
fi

# Provide next steps
echo ""
print_status "Next steps:"
echo "  1. Test in QEMU:    make -C $BUILD_DIR qemu"
echo "  2. Debug with GDB:  make -C $BUILD_DIR qemu-gdb"
echo "  3. Create FS image: make -C $BUILD_DIR fs.img"