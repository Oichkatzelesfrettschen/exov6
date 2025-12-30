# ═══════════════════════════════════════════════════════════════════════════════
# FeuerBird Exokernel - Optimized Build Container
# Rising from the ashes with blazing fast, stable, and compatible build environment
# ═══════════════════════════════════════════════════════════════════════════════
#
# This Dockerfile provides an optimal build environment for FeuerBird Exokernel:
# - Ubuntu 24.04 LTS base for maximum compatibility and glibc support
# - LLVM 18 toolchain with Clang, LLD, Polly optimizations
# - Multi-stage build for minimal final image size
# - BuildKit cache mounts for faster rebuilds
# - All dependencies pre-installed for immediate builds
#
# Build with:
#   docker build -t feuerbird-builder .
# Run with:
#   docker run -v $(pwd):/workspace feuerbird-builder
#
# ═══════════════════════════════════════════════════════════════════════════════

# ─────────────────────────────────────────────────────────────────────────────────
# Stage 1: Builder - Full development environment
# ─────────────────────────────────────────────────────────────────────────────────
FROM ubuntu:24.04 AS builder

# Metadata
LABEL maintainer="FeuerBird Exokernel Project"
LABEL description="Optimized build environment for FeuerBird Exokernel"
LABEL version="1.0.0"

# Prevent interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Set timezone to avoid tzdata prompts
ENV TZ=UTC

# Configure build parallelism (uses all available CPUs)
ARG MAKEFLAGS="-j$(nproc)"
ENV MAKEFLAGS=${MAKEFLAGS}

# LLVM version to install
ARG LLVM_VERSION=18

# ─────────────────────────────────────────────────────────────────────────────────
# Install core system dependencies and LLVM toolchain
# ─────────────────────────────────────────────────────────────────────────────────
RUN --mount=type=cache,target=/var/cache/apt,sharing=locked \
    --mount=type=cache,target=/var/lib/apt,sharing=locked \
    apt-get update && \
    apt-get install -y --no-install-recommends \
        # Core build tools
        build-essential \
        ca-certificates \
        curl \
        git \
        wget \
        # LLVM toolchain
        clang-${LLVM_VERSION} \
        clang++-${LLVM_VERSION} \
        clang-format-${LLVM_VERSION} \
        clang-tidy-${LLVM_VERSION} \
        clangd-${LLVM_VERSION} \
        lld-${LLVM_VERSION} \
        llvm-${LLVM_VERSION} \
        llvm-${LLVM_VERSION}-dev \
        llvm-${LLVM_VERSION}-tools \
        llvm-${LLVM_VERSION}-runtime \
        libc++-${LLVM_VERSION}-dev \
        libc++abi-${LLVM_VERSION}-dev \
        # Build systems
        cmake \
        ninja-build \
        meson \
        pkg-config \
        # Parser generators
        bison \
        flex \
        # Python for build scripts
        python3 \
        python3-pip \
        python3-venv \
        # Kernel development tools
        bc \
        libelf-dev \
        libssl-dev \
        libncurses-dev \
        # QEMU for testing
        qemu-system-x86 \
        qemu-system-arm \
        qemu-system-aarch64 \
        qemu-system-misc \
        qemu-utils \
        # Additional utilities
        file \
        rsync \
        unzip \
        xz-utils \
        vim-tiny \
        less && \
    # Clean up apt cache (not needed with cache mount, but good practice)
    rm -rf /var/lib/apt/lists/*

# ─────────────────────────────────────────────────────────────────────────────────
# Configure LLVM toolchain as default
# ─────────────────────────────────────────────────────────────────────────────────
RUN update-alternatives --install /usr/bin/clang clang /usr/bin/clang-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/clang-format clang-format /usr/bin/clang-format-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/clang-tidy clang-tidy /usr/bin/clang-tidy-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/clangd clangd /usr/bin/clangd-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/llvm-ar llvm-ar /usr/bin/llvm-ar-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/llvm-nm llvm-nm /usr/bin/llvm-nm-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/llvm-objcopy llvm-objcopy /usr/bin/llvm-objcopy-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/llvm-objdump llvm-objdump /usr/bin/llvm-objdump-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/llvm-strip llvm-strip /usr/bin/llvm-strip-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/ld.lld ld.lld /usr/bin/ld.lld-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/opt opt /usr/bin/opt-${LLVM_VERSION} 100

# Set environment variables for LLVM toolchain
ENV CC=clang \
    CXX=clang++ \
    AR=llvm-ar \
    NM=llvm-nm \
    RANLIB=llvm-ranlib \
    OBJCOPY=llvm-objcopy \
    OBJDUMP=llvm-objdump \
    STRIP=llvm-strip

# ─────────────────────────────────────────────────────────────────────────────────
# Install Python development tools
# ─────────────────────────────────────────────────────────────────────────────────
# NOTE: We intentionally use `--break-system-packages` here because this is a
# dedicated, ephemeral builder image based on Ubuntu 24.04 with PEP 668 enabled.
# The system Python environment in this container is not shared with other
# applications or the host OS; it is used solely for build and test tooling.
# Using this flag avoids conflicts with the `EXTERNALLY-MANAGED` protection while
# keeping the rest of the image layout simple. If this image is ever reused as a
# general-purpose base image, consider migrating these tools into a virtualenv.
# NOTE: We use `--break-system-packages` here because this is a dedicated,
# ephemeral builder image based on Ubuntu 24.04 with PEP 668 enabled.
# The system Python environment in this container is not shared with other
# applications or the host OS; it is used solely for build and test tooling.
# Using this flag avoids conflicts with the `EXTERNALLY-MANAGED` protection while
# keeping the image layout simple. If this image is ever reused as a general-purpose
# base image, consider migrating these tools into a virtualenv.
#
# Python dependencies are version-pinned in docker-requirements.txt for supply
# chain security and reproducible builds.
COPY docker-requirements.txt /tmp/docker-requirements.txt
RUN --mount=type=cache,target=/root/.cache/pip \
    pip3 install --break-system-packages --no-cache-dir \
        -r /tmp/docker-requirements.txt && \
    rm /tmp/docker-requirements.txt

# ─────────────────────────────────────────────────────────────────────────────────
# Create non-root user for builds (security best practice)
# ─────────────────────────────────────────────────────────────────────────────────
RUN useradd -m -u 1000 -s /bin/bash builder && \
    mkdir -p /workspace /build && \
    chown -R builder:builder /workspace /build

# ─────────────────────────────────────────────────────────────────────────────────
# Set working directory
# ─────────────────────────────────────────────────────────────────────────────────
WORKDIR /workspace

# Switch to non-root user
USER builder

# ─────────────────────────────────────────────────────────────────────────────────
# Verify toolchain installation
# ─────────────────────────────────────────────────────────────────────────────────
RUN clang --version && \
    clang++ --version && \
    ld.lld --version && \
    cmake --version && \
    ninja --version && \
    meson --version && \
    python3 --version && \
    qemu-system-x86_64 --version | head -n1

# ─────────────────────────────────────────────────────────────────────────────────
# Default command - show available tools
# ─────────────────────────────────────────────────────────────────────────────────
CMD ["/bin/bash", "-c", "echo '═══════════════════════════════════════════════════════════════'; \
    echo 'FeuerBird Exokernel Build Container'; \
    echo '═══════════════════════════════════════════════════════════════'; \
    echo ''; \
    echo 'Toolchain Information:'; \
    echo '  Compiler: '$(clang --version | head -n1); \
    echo '  Linker:   '$(ld.lld --version | head -n1); \
    echo '  CMake:    '$(cmake --version | head -n1); \
    echo '  Ninja:    '$(ninja --version); \
    echo '  Meson:    '$(meson --version); \
    echo '  Python:   '$(python3 --version); \
    echo ''; \
    echo 'Quick Start:'; \
    echo '  CMake Build:  cmake -B build -G Ninja && ninja -C build'; \
    echo '  Meson Build:  meson setup builddir && ninja -C builddir'; \
    echo '  QEMU Test:    ninja -C build qemu-nox'; \
    echo ''; \
    echo 'Volume mounted at: /workspace'; \
    echo '═══════════════════════════════════════════════════════════════'; \
    exec /bin/bash"]

# ─────────────────────────────────────────────────────────────────────────────────
# Stage 2: Runtime - Minimal image for running builds (optional)
# ─────────────────────────────────────────────────────────────────────────────────
FROM ubuntu:24.04 AS runtime

ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# Install only runtime dependencies
RUN --mount=type=cache,target=/var/cache/apt,sharing=locked \
    --mount=type=cache,target=/var/lib/apt,sharing=locked \
    apt-get update && \
    apt-get install -y --no-install-recommends \
        qemu-system-x86 \
        qemu-system-arm \
        qemu-system-aarch64 \
        ca-certificates && \
    rm -rf /var/lib/apt/lists/*

# Create non-root user
RUN useradd -m -u 1000 -s /bin/bash runner && \
    mkdir -p /workspace && \
    chown -R runner:runner /workspace

WORKDIR /workspace
USER runner

# Default runtime image just provides QEMU for testing
CMD ["/bin/bash"]
