# FeuerBird Development Environment Setup Guide

This guide explains how to set up a development environment for the FeuerBird project on a modern Debian-based Linux distribution like Ubuntu 24.04. The original `setup.sh` script is outdated and no longer works on recent OS versions. This guide provides an updated and educational walkthrough of the necessary steps.

## 1. Core Build Tools

These are the essential packages for compiling C/C++ code, as well as common development tools.

```bash
sudo apt-get update
sudo apt-get install -y \
  build-essential gcc g++ clang lld llvm \
  clang-format clang-tidy clangd clang-tools uncrustify astyle editorconfig shellcheck pre-commit \
  make bmake ninja-build cmake meson \
  autoconf automake libtool m4 gawk flex bison byacc \
  pkg-config file ca-certificates curl git unzip graphviz doxygen doxygen-latex \
  libopenblas-dev liblapack-dev libeigen3-dev \
  strace ltrace linux-tools-generic systemtap systemtap-sdt-dev crash \
  valgrind kcachegrind trace-cmd kernelshark \
  libasan6 libubsan1 likwid hwloc cloc cscope universal-ctags cppcheck bear
```

**Notes:**
- `linux-perf` has been replaced with `linux-tools-generic`.
- `ctags` has been replaced with `universal-ctags`.

## 2. Python Environment

This project uses Python for scripting and various tools.

```bash
sudo apt-get install -y \
  python3 python3-pip python3-dev python3-venv python3-wheel \
  python3-sphinx python3-breathe python3-sphinx-rtd-theme python3-myst-parser

pip3 install \
  tensorflow-cpu jax jaxlib \
  tensorflow-model-optimization mlflow onnxruntime-tools \
  black flake8 pyperf py-cpuinfo pytest pre-commit compile-db configuredb \
  lizard radon networkx pygraphviz mypy pylint \
  tlacli tlaplus-jupyter tla
```

**Note:** The `pip3 install` commands may fail if run with `sudo`. It is recommended to run them as a regular user.

## 3. QEMU Emulator

QEMU is used to run and test the kernel.

```bash
sudo apt-get install -y \
  qemu-user-static \
  qemu-system-x86 qemu-system-arm qemu-system-aarch64 \
  qemu-system-riscv64 qemu-system-ppc qemu-system-ppc64 qemu-utils
```
**Note:** The `qemu-nox` package no longer exists and has been removed from the list.

## 4. Cross-Compilers

The project requires several cross-compilers to build for different architectures.

### 4.1. Standard Cross-Compilers (from APT)

```bash
sudo apt-get install -y \
  bcc bin86 elks-libc \
  gcc-multilib g++-multilib \
  binutils-i686-linux-gnu binutils-x86-64-linux-gnu \
  gcc-x86-64-linux-gnu g++-x86-64-linux-gnu \
  gcc-i686-linux-gnu g++-i686-linux-gnu \
  gcc-aarch64-linux-gnu g++-aarch64-linux-gnu \
  gcc-arm-linux-gnueabi g++-arm-linux-gnueabi \
  gcc-arm-linux-gnueabihf g++-arm-linux-gnueabihf \
  gcc-riscv64-linux-gnu g++-riscv64-linux-gnu \
  gcc-powerpc-linux-gnu g++-powerpc-linux-gnu \
  gcc-powerpc64-linux-gnu g++-powerpc64-linux-gnu \
  gcc-powerpc64le-linux-gnu g++-powerpc64le-linux-gnu \
  gcc-m68k-linux-gnu g++-m68k-linux-gnu \
  gcc-hppa-linux-gnu g++-hppa-linux-gnu \
  gcc-mips-linux-gnu g++-mips-linux-gnu \
  gcc-mipsel-linux-gnu g++-mipsel-linux-gnu \
  gcc-mips64-linux-gnuabi64 g++-mips64-linux-gnuabi64 \
  gcc-mips64el-linux-gnuabi64 g++-mips64el-linux-gnuabi64
```
**Note:** The `gcc-ia64-linux-gnu` and `gcc-loongarch64-linux-gnu` cross-compilers are no longer available in modern Ubuntu repositories and have been removed from this list.

### 4.2. Bare-Metal ELF Cross-Compilers (Manual Installation Required)

Building the FeuerBird kernel requires `i386-elf` and `x86_64-elf` cross-compilers. These are **not available** in the standard Ubuntu 24.04 repositories. You must install them manually.

You can download pre-built toolchains from [newos.org](https://newos.org/toolchains/).

```bash
# Download the toolchains
curl -L -o /tmp/i386-elf-7.5.0-Linux-x86_64.tar.xz https://newos.org/toolchains/i386-elf-7.5.0-Linux-x86_64.tar.xz
curl -L -o /tmp/x86_64-elf-7.5.0-Linux-x86_64.tar.xz https://newos.org/toolchains/x86_64-elf-7.5.0-Linux-x86_64.tar.xz

# Create the installation directory
sudo mkdir -p /opt/cross

# Extract the toolchains
sudo tar -xf /tmp/i386-elf-7.5.0-Linux-x86_64.tar.xz -C /opt/cross
sudo tar -xf /tmp/x86_64-elf-7.5.0-Linux-x86_64.tar.xz -C /opt/cross

# Add the toolchains to your PATH
export PATH="/opt/cross/i386-elf-7.5.0-Linux-x86_64/bin:/opt/cross/x86_64-elf-7.5.0-Linux-x86_64/bin:$PATH"

# You should add the export command to your shell's startup file (e.g., ~/.bashrc) to make it permanent.
```

### 4.3. IA-16 Cross-Compiler (Manual Installation)

```bash
# Download and install the IA-16 cross-compiler
IA16_VER=$(curl -fsSL https://api.github.com/repos/tkchia/gcc-ia16/releases/latest | awk -F\\" '/tag_name/{print $4; exit}')
curl -fsSL "https://github.com/tkchia/gcc-ia16/releases/download/${IA16_VER}/ia16-elf-gcc-linux64.tar.xz" | sudo tar -Jx -C /opt

# Add it to your PATH
echo 'export PATH=/opt/ia16-elf-gcc/bin:$PATH' | sudo tee /etc/profile.d/ia16.sh
export PATH=/opt/ia16-elf-gcc/bin:$PATH
```

## 5. Other Runtimes and Tools

This project also lists dependencies for a wide variety of other programming languages and frameworks. Install these as needed.

```bash
sudo apt-get install -y \
  golang-go \
  rustc cargo clippy rustfmt \
  lua5.4 liblua5.4-dev luarocks \
  ghc cabal-install hlint stylish-haskell \
  sbcl ecl clisp cl-quicklisp slime cl-asdf \
  ldc gdc dmd-compiler dub libphobos-dev \
  chicken-bin libchicken-dev chicken-doc \
  openjdk-17-jdk maven gradle dotnet-sdk-8 mono-complete \
  swift swift-lldb swiftpm swift-tools-support-core libswiftFuzzer \
  kotlin gradle-plugin-kotlin \
  ruby ruby-dev gem bundler php-cli php-dev composer phpunit \
  r-base r-base-dev dart flutter gnat gprbuild gfortran gnucobol nodejs npm \
  fpc lazarus zig nim nimble crystal shards gforth
```

## 6. Final Steps

### Create gmake alias
```bash
sudo ln -s "$(command -v make)" /usr/local/bin/gmake
```

### Install protoc
```bash
PROTO_VERSION=25.1
curl -fsSL "https://raw.githubusercontent.com/protocolbuffers/protobuf/v${PROTO_VERSION}/protoc-${PROTO_VERSION}-linux-x86_64.zip" -o /tmp/protoc.zip
sudo unzip -d /usr/local /tmp/protoc.zip
rm /tmp/protoc.zip
```
