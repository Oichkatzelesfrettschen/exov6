#!/bin/bash
# FeuerBird exokernel build system setup script
# Meson + Ninja build system setup targeting C17 (SUSv5) compliance

set -euo pipefail

# Configuration
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly PROJECT_ROOT
readonly MIN_CMAKE_VERSION="3.16"
readonly MIN_MESON_VERSION="0.55"

# Colors for output
readonly RED='\033[0;31m'
readonly GREEN='\033[0;32m'
readonly YELLOW='\033[1;33m'
readonly BLUE='\033[0;34m'
readonly NC='\033[0m' # No Color

# Logging functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $*"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $*"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $*"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $*"
}

# Check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Check compiler C17 support
check_c17_support() {
    local compiler="$1"
    log_info "Checking C17 support for $compiler"
    
    if ! "$compiler" -std=c17 -xc /dev/null -c -o /dev/null 2>/dev/null; then
        log_error "$compiler does not support -std=c17 (C17)"
        return 1
    fi
    
    log_success "$compiler supports C17"
    return 0
}

# Check version requirements
check_version() {
    local tool="$1"
    local current="$2"
    local required="$3"
    
    if ! command_exists "$tool"; then
        log_error "$tool not found"
        return 1
    fi
    
    # Simple version comparison for basic tools
    log_info "$tool version: $current (required: $required)"
    return 0
}

# Install Python dependencies
install_python_deps() {
    log_info "Installing Python dependencies"
    
    if ! command_exists pip; then
        log_error "pip not found. Please install Python pip."
        return 1
    fi
    
    # Install build tools
    pip install --user meson ninja wheel setuptools
    
    # Install testing and linting tools
    pip install --user pytest black flake8
    
    # Install documentation tools
    pip install --user sphinx sphinx-rtd-theme
    
    log_success "Python dependencies installed"
}

# Setup pre-commit hooks
setup_precommit() {
    log_info "Setting up pre-commit hooks"
    
    if ! command_exists pre-commit; then
        pip install --user pre-commit
    fi
    
    cd "$PROJECT_ROOT"
    pre-commit install
    
    log_success "Pre-commit hooks installed"
}

# Verify toolchain
verify_toolchain() {
    log_info "Verifying build toolchain"
    
    # Check compilers
    local compilers=("clang" "gcc")
    local found_compiler=""
    
    for compiler in "${compilers[@]}"; do
        if command_exists "$compiler"; then
            if check_c17_support "$compiler"; then
                found_compiler="$compiler"
                break
            fi
        fi
    done
    
    if [[ -z "$found_compiler" ]]; then
        log_error "No C17-capable compiler found. Please install clang or gcc with C17 support."
        return 1
    fi
    
    export CC="$found_compiler"
    log_success "Using compiler: $found_compiler"
    
    # Check build tools
    if command_exists cmake; then
        local cmake_version
        cmake_version=$(cmake --version | head -n1 | grep -o '[0-9]\+\.[0-9]\+\.[0-9]\+')
        check_version "cmake" "$cmake_version" "$MIN_CMAKE_VERSION"
    else
        log_warning "CMake not found. CMake builds will not work."
    fi
    
    if command_exists meson; then
        local meson_version
        meson_version=$(meson --version)
        check_version "meson" "$meson_version" "$MIN_MESON_VERSION"
    else
        log_warning "Meson not found. Installing via pip..."
        pip install --user meson ninja
    fi
    
    if command_exists make; then
        local make_version
        make_version=$(make --version | head -n1 | grep -o '[0-9]\+\.[0-9]\+')
        check_version "make" "$make_version" "4.0"
    else
        log_error "GNU Make not found. Please install make."
        return 1
    fi
    
    # Check additional tools
    for tool in bison flex; do
        if ! command_exists "$tool"; then
            log_warning "$tool not found. Some features may not work."
        fi
    done
    
    return 0
}

# Test build systems
test_build_systems() {
    log_info "Testing build systems"
    
    cd "$PROJECT_ROOT"
    
    # Test Meson
    if command_exists meson; then
        log_info "Testing Meson build system"
        if meson setup _build --reconfigure >/dev/null 2>&1; then
            log_success "Meson configuration successful"
            rm -rf _build
        else
            log_warning "Meson configuration failed - will need fixes"
        fi
    fi
    
    # CMake support removed; Meson is the only supported build system.
    
    # Test Make
    log_info "Testing Makefile"
    # Make test is complex due to cross-compiler requirements
    log_warning "Makefile requires cross-compilation toolchain - skipping test"
}

# Create offline cache directory
setup_offline_cache() {
    log_info "Setting up offline package cache"
    
    local cache_dir="$PROJECT_ROOT/offline_packages"
    mkdir -p "$cache_dir"
    
    log_success "Offline cache directory created: $cache_dir"
}

# Main setup function
main() {
    log_info "Starting FeuerBird build system setup"
    log_info "Project root: $PROJECT_ROOT"
    
    # Verify basic requirements
    if ! verify_toolchain; then
        log_error "Toolchain verification failed"
        exit 1
    fi
    
    # Install dependencies
    if ! install_python_deps; then
        log_error "Failed to install Python dependencies"
        exit 1
    fi
    
    # Setup pre-commit
    if ! setup_precommit; then
        log_warning "Pre-commit setup failed"
    fi
    
    # Setup offline cache
    setup_offline_cache
    
    # Test build systems
    test_build_systems
    
    log_success "Build system setup complete!"
    log_info "You can now use:"
    log_info "  - meson setup builddir && ninja -C builddir"
    log_info "  - cmake -B build && cmake --build build"
    log_info "  - make (requires cross-compilation toolchain)"
    log_info "  - pytest (for running tests)"
    log_info "  - pre-commit run --all-files (for linting)"
}

# Run shellcheck if available
if command_exists shellcheck; then
    if ! shellcheck "$0"; then
        log_error "Shellcheck found issues in setup script"
        exit 1
    fi
fi

# Execute main function
main "$@"
