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
    # Advanced static analysis
    sparse \
    splint \
    flawfinder \
    rats \
    # Formal verification tools
    coq \
    # Dynamic analysis
    valgrind \
    linux-tools-generic \
    # Complexity analysis
    python3-lizard \
    # Code transformation
    astyle \
    uncrustify \
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
    cmakelang==0.6.13 \
    semgrep==1.55.2 \
    lizard==1.17.10

# ─────────────────────────────────────────────────────────────────────────────────
# Install Z3 Theorem Prover with checksum verification
# ─────────────────────────────────────────────────────────────────────────────────
RUN Z3_VERSION=4.12.2 && \
    Z3_SHA256=9f58f3710bd2094085951a75791550f547903d75fe7e2fcb373c5f03fc761b8f && \
    wget https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-glibc-2.35.zip && \
    echo "${Z3_SHA256}  z3-${Z3_VERSION}-x64-glibc-2.35.zip" | sha256sum -c - && \
    unzip z3-${Z3_VERSION}-x64-glibc-2.35.zip && \
    cp z3-${Z3_VERSION}-x64-glibc-2.35/bin/z3 /usr/local/bin/ && \
    rm -rf z3-${Z3_VERSION}-x64-glibc-2.35*

# ─────────────────────────────────────────────────────────────────────────────────
# Install TLA+ Tools with checksum verification
# ─────────────────────────────────────────────────────────────────────────────────
RUN TLA_VERSION=1.8.0 && \
    TLA_SHA256=99b8ac649829a0b19f3990a1d32a5dfc8de2f5f85ff3de2a05c0f9b3c5dabb61 && \
    wget https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar -O /usr/local/bin/tla2tools.jar && \
    echo "${TLA_SHA256}  /usr/local/bin/tla2tools.jar" | sha256sum -c - && \
    cat << 'EOF' > /usr/local/bin/tlc
#!/bin/bash

# Ensure Java is available
if ! command -v java >/dev/null 2>&1; then
    echo "Error: 'java' is not installed or not found in PATH." >&2
    exit 1
fi

# Ensure the TLA+ tools JAR is accessible
if [ ! -r /usr/local/bin/tla2tools.jar ]; then
    echo "Error: TLA+ tools JAR '/usr/local/bin/tla2tools.jar' not found or not readable." >&2
    exit 1
fi

exec java -jar /usr/local/bin/tla2tools.jar "$@"
EOF
RUN chmod +x /usr/local/bin/tlc

# ─────────────────────────────────────────────────────────────────────────────────
# Install FlameGraph Tools with pinned commit SHA
# ─────────────────────────────────────────────────────────────────────────────────
RUN FLAMEGRAPH_COMMIT=cd9ee4c4449775a2f867acf31c84b7fe4b132ad5 && \
    git clone https://github.com/brendangregg/FlameGraph /opt/flamegraph && \
    cd /opt/flamegraph && \
    git checkout ${FLAMEGRAPH_COMMIT} && \
    ln -s /opt/flamegraph/flamegraph.pl /usr/local/bin/flamegraph.pl && \
    ln -s /opt/flamegraph/stackcollapse-perf.pl /usr/local/bin/stackcollapse-perf.pl

# ─────────────────────────────────────────────────────────────────────────────────
# Install Facebook Infer with checksum verification
# ─────────────────────────────────────────────────────────────────────────────────
RUN INFER_VERSION=1.1.0 && \
    INFER_SHA256=2f850e794d9f7bc87c3c9a827d85f5e5e88bb2e6088c4f05a9b3a69a96e3f6a5 && \
    wget https://github.com/facebook/infer/releases/download/v${INFER_VERSION}/infer-linux64-v${INFER_VERSION}.tar.xz && \
    echo "${INFER_SHA256}  infer-linux64-v${INFER_VERSION}.tar.xz" | sha256sum -c - && \
    tar -xJf infer-linux64-v${INFER_VERSION}.tar.xz && \
    mv infer-linux64-v${INFER_VERSION} /opt/infer && \
    ln -s /opt/infer/bin/infer /usr/local/bin/infer && \
    rm infer-linux64-v${INFER_VERSION}.tar.xz

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
