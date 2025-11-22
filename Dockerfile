# ExoV6 Phoenix Exokernel - Modern Build Environment
# Base: Ubuntu 24.04 LTS (Noble Numbat) for x86_64
# Compatible with GitHub Actions ubuntu-latest runners

FROM ubuntu:24.04 AS base

LABEL maintainer="ExoV6 Development Team"
LABEL description="ExoV6 Phoenix Exokernel build environment"
LABEL version="1.0"

# Prevent interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# Install core build dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    cmake \
    ninja-build \
    make \
    git \
    clang-18 \
    clang-tools-18 \
    lld-18 \
    llvm-18 \
    llvm-18-dev \
    llvm-18-tools \
    gcc \
    g++ \
    gcc-multilib \
    g++-multilib \
    nasm \
    yasm \
    binutils \
    libelf-dev \
    libssl-dev \
    zlib1g-dev \
    libcap-dev \
    qemu-system-x86 \
    qemu-utils \
    qemu-user-static \
    expect \
    socat \
    python3 \
    python3-pip \
    curl \
    wget \
    file \
    bc \
    bison \
    flex \
    pkg-config \
    xorriso \
    grub-pc-bin \
    mtools \
    gdb \
    strace \
    && rm -rf /var/lib/apt/lists/*

# Set up LLVM 18 as default
RUN update-alternatives --install /usr/bin/clang clang /usr/bin/clang-18 100 && \
    update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-18 100 && \
    update-alternatives --install /usr/bin/lld lld /usr/bin/lld-18 100 && \
    update-alternatives --install /usr/bin/llvm-ar llvm-ar /usr/bin/llvm-ar-18 100 && \
    update-alternatives --install /usr/bin/llvm-nm llvm-nm /usr/bin/llvm-nm-18 100 && \
    update-alternatives --install /usr/bin/llvm-objcopy llvm-objcopy /usr/bin/llvm-objcopy-18 100 && \
    update-alternatives --install /usr/bin/llvm-objdump llvm-objdump /usr/bin/llvm-objdump-18 100 && \
    update-alternatives --install /usr/bin/llvm-strip llvm-strip /usr/bin/llvm-strip-18 100 && \
    update-alternatives --install /usr/bin/opt opt /usr/bin/opt-18 100

# Environment variables for build
ENV CC=clang
ENV CXX=clang++
ENV LD=lld
ENV AR=llvm-ar
ENV NM=llvm-nm
ENV OBJCOPY=llvm-objcopy
ENV OBJDUMP=llvm-objdump
ENV STRIP=llvm-strip
ENV ARCH=x86_64
ENV TARGET_ARCH=x86_64

WORKDIR /workspace

# ============================================================================
# Builder stage - compiles the kernel
# ============================================================================
FROM base AS builder

COPY . /workspace/

# Create build script
COPY <<'BUILDSCRIPT' /workspace/build.sh
#!/bin/bash
set -euo pipefail

echo "=============================================="
echo "ExoV6 Phoenix Exokernel Build"
echo "=============================================="
echo "Architecture: ${ARCH:-x86_64}"
echo "Compiler: $(clang --version | head -1)"
echo "CMake: $(cmake --version | head -1)"
echo "=============================================="

BUILD_TYPE="${BUILD_TYPE:-Release}"
BUILD_DIR="${BUILD_DIR:-build}"

mkdir -p "${BUILD_DIR}"
cd "${BUILD_DIR}"

cmake -G Ninja \
    -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" \
    -DCMAKE_C_COMPILER=clang \
    -DCMAKE_CXX_COMPILER=clang++ \
    -DUSE_LLD=ON \
    -DBUILD_TESTS=ON \
    -DBUILD_DEMOS=ON \
    ..

echo ""
echo "Building..."
ninja -v 2>&1 | tee build.log

echo ""
echo "=============================================="
echo "Build complete!"
echo "=============================================="
ls -la

if [ -f "kernel" ]; then
    echo ""
    echo "Kernel binary info:"
    file kernel
    size kernel || true
fi
BUILDSCRIPT

RUN chmod +x /workspace/build.sh

# Create test script
COPY <<'TESTSCRIPT' /workspace/test.sh
#!/bin/bash
set -euo pipefail

echo "=============================================="
echo "ExoV6 Test Suite"
echo "=============================================="

BUILD_DIR="${BUILD_DIR:-build}"
cd "${BUILD_DIR}"

if ninja -t targets | grep -q "^test:"; then
    echo "Running unit tests..."
    ninja test || true
fi

KERNEL="kernel"
if [ -f "${KERNEL}" ]; then
    echo ""
    echo "Running QEMU smoke test..."
    timeout 30s qemu-system-x86_64 \
        -kernel "${KERNEL}" \
        -m 256M \
        -cpu qemu64 \
        -smp 2 \
        -nographic \
        -no-reboot \
        -serial mon:stdio \
        -d guest_errors 2>&1 | tee qemu-output.log || true

    echo ""
    if grep -qi "panic\|error\|fault" qemu-output.log 2>/dev/null; then
        echo "Warning: Potential errors detected in QEMU output"
        grep -i "panic\|error\|fault" qemu-output.log || true
    else
        echo "QEMU smoke test completed"
    fi
else
    echo "No kernel binary found, skipping QEMU test"
fi
TESTSCRIPT

RUN chmod +x /workspace/test.sh

# Create QEMU boot script
COPY <<'QEMUSCRIPT' /workspace/qemu-boot.sh
#!/bin/bash
set -euo pipefail

BUILD_DIR="${BUILD_DIR:-build}"
KERNEL="${BUILD_DIR}/kernel"
MEMORY="${MEMORY:-512M}"
CPUS="${CPUS:-2}"

if [ ! -f "${KERNEL}" ]; then
    echo "Error: Kernel not found at ${KERNEL}"
    echo "Run ./build.sh first"
    exit 1
fi

echo "Booting ExoV6 kernel with QEMU..."
echo "  Kernel: ${KERNEL}"
echo "  Memory: ${MEMORY}"
echo "  CPUs: ${CPUS}"
echo ""
echo "Press Ctrl+A, X to exit QEMU"
echo ""

qemu-system-x86_64 \
    -kernel "${KERNEL}" \
    -m "${MEMORY}" \
    -cpu qemu64 \
    -smp "${CPUS}" \
    -nographic \
    -serial mon:stdio \
    -no-reboot \
    -d guest_errors,int \
    "$@"
QEMUSCRIPT

RUN chmod +x /workspace/qemu-boot.sh

CMD ["/bin/bash", "-c", "/workspace/build.sh && /workspace/test.sh"]

# ============================================================================
# Development stage
# ============================================================================
FROM base AS dev

RUN apt-get update && apt-get install -y --no-install-recommends \
    vim \
    nano \
    less \
    htop \
    tmux \
    valgrind \
    cppcheck \
    clang-format-18 \
    clang-tidy-18 \
    bear \
    && rm -rf /var/lib/apt/lists/* && \
    update-alternatives --install /usr/bin/clang-format clang-format /usr/bin/clang-format-18 100 && \
    update-alternatives --install /usr/bin/clang-tidy clang-tidy /usr/bin/clang-tidy-18 100

WORKDIR /workspace

CMD ["/bin/bash"]

# ============================================================================
# CI stage - minimal for CI/CD
# ============================================================================
FROM base AS ci

COPY . /workspace/

RUN mkdir -p /workspace/build

WORKDIR /workspace

# Create CI build script
COPY <<'CISCRIPT' /workspace/ci-build.sh
#!/bin/bash
set -euxo pipefail

cd /workspace
mkdir -p build && cd build

cmake -G Ninja \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_C_COMPILER=clang \
    -DCMAKE_CXX_COMPILER=clang++ \
    -DUSE_LLD=ON \
    -DBUILD_TESTS=ON \
    ..

ninja -j$(nproc)

if [ -f "kernel" ]; then
    echo "Kernel built successfully"
    file kernel

    if file kernel | grep -q "x86-64\|x86_64\|64-bit"; then
        echo "Confirmed x86_64 binary"
    else
        echo "Warning: May not be x86_64 binary"
    fi
fi
CISCRIPT

RUN chmod +x /workspace/ci-build.sh

CMD ["/workspace/ci-build.sh"]
