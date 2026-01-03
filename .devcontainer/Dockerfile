# ═══════════════════════════════════════════════════════════════════════════════
# FeuerBird Exokernel - Dev Container Dockerfile
# Optimized development environment with all necessary tools
# ═══════════════════════════════════════════════════════════════════════════════

FROM ubuntu:24.04

# Prevent interactive prompts
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# LLVM version
ARG LLVM_VERSION=18

# ─────────────────────────────────────────────────────────────────────────────────
# Install all development dependencies
# ─────────────────────────────────────────────────────────────────────────────────
RUN apt-get update && apt-get install -y --no-install-recommends \
    # Core build tools
    build-essential \
    ca-certificates \
    curl \
    git \
    wget \
    sudo \
    # LLVM toolchain with all extras
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
    ccache \
    # Parser generators
    bison \
    flex \
    # Python
    python3 \
    python3-pip \
    python3-venv \
    # Static analysis tools
    cppcheck \
    clang-tools-${LLVM_VERSION} \
    include-what-you-use \
    # Coverage tools
    lcov \
    gcovr \
    # Kernel development
    bc \
    libelf-dev \
    libssl-dev \
    libncurses-dev \
    # QEMU
    qemu-system-x86 \
    qemu-system-arm \
    qemu-system-aarch64 \
    qemu-utils \
    # Debugging
    gdb \
    gdb-multiarch \
    valgrind \
    strace \
    ltrace \
    # Documentation
    doxygen \
    graphviz \
    texlive-latex-base \
    # Utilities
    file \
    rsync \
    unzip \
    xz-utils \
    vim \
    nano \
    less \
    tree \
    htop \
    shellcheck \
    # Version control
    git-lfs \
    && rm -rf /var/lib/apt/lists/*

# ─────────────────────────────────────────────────────────────────────────────────
# Configure LLVM toolchain
# ─────────────────────────────────────────────────────────────────────────────────
RUN update-alternatives --install /usr/bin/clang clang /usr/bin/clang-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/clang-format clang-format /usr/bin/clang-format-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/clang-tidy clang-tidy /usr/bin/clang-tidy-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/clangd clangd /usr/bin/clangd-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/llvm-ar llvm-ar /usr/bin/llvm-ar-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/llvm-nm llvm-nm /usr/bin/llvm-nm-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/llvm-cov llvm-cov /usr/bin/llvm-cov-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/llvm-profdata llvm-profdata /usr/bin/llvm-profdata-${LLVM_VERSION} 100 && \
    update-alternatives --install /usr/bin/ld.lld ld.lld /usr/bin/ld.lld-${LLVM_VERSION} 100

# Set environment for LLVM
ENV CC=clang \
    CXX=clang++ \
    AR=llvm-ar \
    NM=llvm-nm \
    RANLIB=llvm-ranlib

# ─────────────────────────────────────────────────────────────────────────────────
# Install Python development tools
# ─────────────────────────────────────────────────────────────────────────────────
RUN pip3 install --break-system-packages \
    pytest==8.3.3 \
    pytest-cov==6.0.0 \
    pytest-xdist==3.6.1 \
    pre-commit==4.0.1 \
    black==24.10.0 \
    flake8==7.1.1 \
    mypy==1.13.0 \
    sphinx==8.1.3 \
    sphinx-rtd-theme==3.0.2 \
    meson==1.6.1 \
    ninja==1.11.1.1 \
    cmake-format==0.6.13 \
    cmakelang==0.6.13

# ─────────────────────────────────────────────────────────────────────────────────
# Create development user
# ─────────────────────────────────────────────────────────────────────────────────
RUN useradd -m -u 1000 -G sudo -s /bin/bash vscode && \
    echo "vscode ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers && \
    mkdir -p /workspace /home/vscode/.ccache /home/vscode/.cmake && \
    chown -R vscode:vscode /workspace /home/vscode

# ─────────────────────────────────────────────────────────────────────────────────
# Configure ccache
# ─────────────────────────────────────────────────────────────────────────────────
RUN ccache --set-config=max_size=5G && \
    ccache --set-config=compression=true && \
    ccache --set-config=compression_level=6

# ─────────────────────────────────────────────────────────────────────────────────
# Setup working directory
# ─────────────────────────────────────────────────────────────────────────────────
WORKDIR /workspace
USER vscode

# ─────────────────────────────────────────────────────────────────────────────────
# Verify installation
# ─────────────────────────────────────────────────────────────────────────────────
RUN clang --version && \
    cmake --version && \
    ninja --version && \
    python3 --version && \
    ccache --version

CMD ["/bin/bash"]
