#!/bin/bash
# ═══════════════════════════════════════════════════════════════════════════════
# FeuerBird Exokernel - Docker Build Helper Script
# Optimized container-based build workflow
# ═══════════════════════════════════════════════════════════════════════════════

set -euo pipefail

# ─────────────────────────────────────────────────────────────────────────────
# Configuration
# ─────────────────────────────────────────────────────────────────────────────
readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
readonly IMAGE_NAME="feuerbird-builder"
readonly CONTAINER_NAME="feuerbird-build"

# Colors for output
readonly RED='\033[0;31m'
readonly GREEN='\033[0;32m'
readonly YELLOW='\033[1;33m'
readonly BLUE='\033[0;34m'
readonly MAGENTA='\033[0;35m'
readonly CYAN='\033[0;36m'
readonly NC='\033[0m' # No Color

# ─────────────────────────────────────────────────────────────────────────────
# Logging functions
# ─────────────────────────────────────────────────────────────────────────────
log_info() {
    echo -e "${BLUE}[INFO]${NC} $*"
}

log_success() {
    echo -e "${GREEN}[✓]${NC} $*"
}

log_warning() {
    echo -e "${YELLOW}[⚠]${NC} $*"
}

log_error() {
    echo -e "${RED}[✗]${NC} $*"
}

log_header() {
    echo -e "${MAGENTA}═══════════════════════════════════════════════════════════════${NC}"
    echo -e "${MAGENTA}$*${NC}"
    echo -e "${MAGENTA}═══════════════════════════════════════════════════════════════${NC}"
}

# ─────────────────────────────────────────────────────────────────────────────
# Check if Docker is available
# ─────────────────────────────────────────────────────────────────────────────
check_docker() {
    if ! command -v docker &> /dev/null; then
        log_error "Docker is not installed or not in PATH"
        log_info "Please install Docker: https://docs.docker.com/get-docker/"
        exit 1
    fi
    
    if ! docker info &> /dev/null; then
        log_error "Docker daemon is not running or not accessible"
        log_info "Please start Docker daemon or check permissions"
        exit 1
    fi
    
    log_success "Docker is available"
}

# ─────────────────────────────────────────────────────────────────────────────
# Build the Docker image
# ─────────────────────────────────────────────────────────────────────────────
build_image() {
    log_header "Building FeuerBird Build Container"
    
    cd "${PROJECT_ROOT}"
    
    # Check if BuildKit is available
    if docker buildx version &> /dev/null; then
        log_info "Using Docker BuildKit for optimized builds"
        export DOCKER_BUILDKIT=1
    fi
    
    # Build with progress output
    log_info "Building image ${IMAGE_NAME}..."
    if docker build \
        --target builder \
        --tag "${IMAGE_NAME}:latest" \
        --tag "${IMAGE_NAME}:$(date +%Y%m%d)" \
        --build-arg LLVM_VERSION=18 \
        --build-arg MAKEFLAGS="-j$(nproc 2>/dev/null || echo 4)" \
        .; then
        log_success "Image built successfully: ${IMAGE_NAME}:latest"
    else
        log_error "Failed to build Docker image"
        exit 1
    fi
}

# ─────────────────────────────────────────────────────────────────────────────
# Run a build inside the container
# ─────────────────────────────────────────────────────────────────────────────
run_build() {
    local build_system="${1:-cmake}"
    local build_type="${2:-RelWithDebInfo}"
    
    log_header "Running ${build_system} Build"
    
    cd "${PROJECT_ROOT}"
    
    case "${build_system}" in
        cmake)
            docker run --rm \
                -v "${PROJECT_ROOT}:/workspace" \
                -e CMAKE_BUILD_TYPE="${build_type}" \
                -e MAKEFLAGS="-j$(nproc 2>/dev/null || echo 4)" \
                "${IMAGE_NAME}:latest" \
                bash -c "
                    set -euo pipefail
                    cmake -B build -G Ninja \
                        -DCMAKE_BUILD_TYPE=${build_type} \
                        -DUSE_LLD=ON
                    ninja -C build kernel
                "
            ;;
        
        meson)
            docker run --rm \
                -v "${PROJECT_ROOT}:/workspace" \
                -e MAKEFLAGS="-j$(nproc 2>/dev/null || echo 4)" \
                "${IMAGE_NAME}:latest" \
                bash -c "
                    set -euo pipefail
                    meson setup builddir --reconfigure --buildtype=${build_type}
                    ninja -C builddir kernel
                "
            ;;
        
        *)
            log_error "Unknown build system: ${build_system}"
            log_info "Supported: cmake, meson"
            exit 1
            ;;
    esac
    
    log_success "Build completed successfully"
}

# ─────────────────────────────────────────────────────────────────────────────
# Run interactive shell in container
# ─────────────────────────────────────────────────────────────────────────────
run_shell() {
    log_header "Starting Interactive Shell"
    
    cd "${PROJECT_ROOT}"
    
    docker run --rm -it \
        -v "${PROJECT_ROOT}:/workspace" \
        -e TERM=xterm-256color \
        "${IMAGE_NAME}:latest" \
        /bin/bash
}

# ─────────────────────────────────────────────────────────────────────────────
# Run tests in container
# ─────────────────────────────────────────────────────────────────────────────
run_tests() {
    log_header "Running Tests"
    
    cd "${PROJECT_ROOT}"
    
    docker run --rm \
        -v "${PROJECT_ROOT}:/workspace" \
        "${IMAGE_NAME}:latest" \
        bash -c "
            set -euo pipefail
            if [ -f pytest.ini ]; then
                pytest -v tests/ || true
            fi
            if [ -d build ]; then
                cd build && ctest --output-on-failure || true
            fi
        "
}

# ─────────────────────────────────────────────────────────────────────────────
# Clean build artifacts
# ─────────────────────────────────────────────────────────────────────────────
clean_build() {
    log_header "Cleaning Build Artifacts"
    
    cd "${PROJECT_ROOT}"
    
    log_info "Removing build directories..."
    rm -rf build builddir _build _build-* build-*
    
    log_success "Build artifacts cleaned"
}

# ─────────────────────────────────────────────────────────────────────────────
# Show container info
# ─────────────────────────────────────────────────────────────────────────────
show_info() {
    log_header "FeuerBird Build Container Information"
    
    if docker images "${IMAGE_NAME}" --format "table {{.Repository}}\t{{.Tag}}\t{{.Size}}\t{{.CreatedAt}}" | grep -v REPOSITORY; then
        log_success "Container images found"
    else
        log_warning "No container images found. Run 'build' command first."
    fi
    
    echo ""
    log_info "Toolchain in container:"
    docker run --rm "${IMAGE_NAME}:latest" bash -c "
        echo '  Compiler: '\$(clang --version | head -n1)
        echo '  Linker:   '\$(ld.lld --version | head -n1)
        echo '  CMake:    '\$(cmake --version | head -n1)
        echo '  Ninja:    '\$(ninja --version)
        echo '  Meson:    '\$(meson --version)
    " 2>/dev/null || log_warning "Image not built yet"
}

# ─────────────────────────────────────────────────────────────────────────────
# Performance benchmark
# ─────────────────────────────────────────────────────────────────────────────
benchmark() {
    log_header "Running Build Performance Benchmark"
    
    cd "${PROJECT_ROOT}"
    
    # Clean first
    clean_build
    
    log_info "Benchmarking CMake build (cold cache)..."
    local start_time=$(date +%s)
    
    docker run --rm \
        -v "${PROJECT_ROOT}:/workspace" \
        "${IMAGE_NAME}:latest" \
        bash -c "
            set -euo pipefail
            time cmake -B build -G Ninja -DCMAKE_BUILD_TYPE=Release -DUSE_LLD=ON
            time ninja -C build kernel
        " 2>&1 | tee /tmp/benchmark.log
    
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    
    log_success "Benchmark completed in ${duration} seconds"
    
    # Show summary
    echo ""
    log_info "Build summary:"
    if [ -f "${PROJECT_ROOT}/build/kernel" ]; then
        ls -lh "${PROJECT_ROOT}/build/kernel"
        file "${PROJECT_ROOT}/build/kernel"
    fi
}

# ─────────────────────────────────────────────────────────────────────────────
# Show help
# ─────────────────────────────────────────────────────────────────────────────
show_help() {
    cat << EOF
FeuerBird Exokernel - Docker Build Helper

Usage: $0 <command> [options]

Commands:
    build               Build the Docker container image
    cmake [type]        Build with CMake (type: Debug, Release, RelWithDebInfo)
    meson [type]        Build with Meson (type: debug, release, debugoptimized)
    shell               Start interactive shell in container
    test                Run tests in container
    clean               Clean build artifacts
    info                Show container and toolchain information
    benchmark           Run build performance benchmark
    help                Show this help message

Examples:
    $0 build                    # Build the container image
    $0 cmake Release            # Build kernel with CMake (Release)
    $0 meson debugoptimized     # Build kernel with Meson
    $0 shell                    # Start interactive shell
    $0 benchmark                # Run performance benchmark

Environment Variables:
    DOCKER_BUILDKIT=1           Enable BuildKit for faster builds
    BUILD_CPUS=8                Number of CPUs for parallel builds

EOF
}

# ─────────────────────────────────────────────────────────────────────────────
# Main entry point
# ─────────────────────────────────────────────────────────────────────────────
main() {
    # Check Docker first
    check_docker
    
    # Parse command
    local command="${1:-help}"
    shift || true
    
    case "${command}" in
        build)
            build_image
            ;;
        cmake)
            run_build "cmake" "${1:-RelWithDebInfo}"
            ;;
        meson)
            run_build "meson" "${1:-debugoptimized}"
            ;;
        shell)
            run_shell
            ;;
        test)
            run_tests
            ;;
        clean)
            clean_build
            ;;
        info)
            show_info
            ;;
        benchmark)
            benchmark
            ;;
        help|--help|-h)
            show_help
            ;;
        *)
            log_error "Unknown command: ${command}"
            echo ""
            show_help
            exit 1
            ;;
    esac
}

# Run main function
main "$@"
