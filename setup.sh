#!/usr/bin/env bash
set -e

# Update package lists
sudo apt-get update -y

# Install build essentials and specific compiler versions
sudo apt-get install -y build-essential=12.9~deb12u1 \
  gcc-12=12.2.0-14 \
  g++-12=12.2.0-14 \
  clang-17=1:17.0.6-3 \
  make=4.3-5.1 \
  gmake=4.3-5.1 \
  bmake=20230601-1 \
  cmake=3.28.1-1 \
  qemu-system-x86=1:8.1.2+dfsg-5 \
  qemu-utils=1:8.1.2+dfsg-5 \
  nasm=2.16.01-1 \
  x86_64-elf-gcc=13+dfsg-3 \
  x86_64-elf-binutils=2.41-2 \
  gcc-multilib=12.2.0-14 \
  python3=3.11.2-6 \
  python3-pip=23.2.1+dfsg-1 \
  golang-go=2:1.21.1-1 \
  nodejs=18.18.2+dfsg-5 \
  npm=9.5.1~ds-1 \
  rustc=1.75.0+dfsg0-1 \
  cargo=1.75.0+dfsg0-1 \
  curl=7.88.1-10

# Install protoc using curl and bash
curl -fsSL https://raw.githubusercontent.com/protocolbuffers/protobuf/v25.1/install.sh | bash -s -- --version v25.1
#!/bin/bash
set -euo pipefail

# Ensure noninteractive apt
export DEBIAN_FRONTEND=noninteractive

CLANG_VERSION=19
NODE_MAJOR=20
PROTOC_VERSION=25.1
RUST_VERSION=1.76.0

apt-get update
apt-get install -y --no-install-recommends \
  build-essential=12.10* \
  gcc=4:13.* \
  g++=4:13.* \
  gcc-multilib=4:13.* \
  g++-multilib=4:13.* \
  gcc-aarch64-linux-gnu=4:13.* \
  gcc-arm-linux-gnueabihf=4:13.* \
  gcc-riscv64-linux-gnu=4:13.* \
  clang-$CLANG_VERSION \
  lld-$CLANG_VERSION \
  llvm-$CLANG_VERSION \
  cmake=3.* \
  make=4.* \
  bmake=2020.* \
  git=1:2.* \
  curl=8.* \
  unzip=6.* \
  python3=3.* \
  python3-pip=23.* \
  qemu-system-x86=1:8.* \
  qemu-system-arm=1:8.* \
  qemu-system-mips=1:8.* \
  qemu-system-aarch64=1:8.* \
  pkg-config=0.3* \
  file=1:5.* \
  flex=2.* \
  bison=3.* \
  gawk=1:5.* \
  libelf-dev=0.* \
  libncurses5-dev=6.* \
  libssl-dev=3.* \
  libexpat1-dev=2.*

# Create gmake symlink if not present
if ! command -v gmake >/dev/null 2>&1; then
    ln -s $(command -v make) /usr/local/bin/gmake || true
fi

# Install Node from NodeSource
curl -fsSL https://deb.nodesource.com/setup_${NODE_MAJOR}.x | bash -
apt-get install -y --no-install-recommends nodejs=20.*

# Install Rust via rustup
curl https://sh.rustup.rs -sSf | bash -s -- -y --default-toolchain ${RUST_VERSION}
export PATH="$HOME/.cargo/bin:$PATH"

# Install protoc
curl -L https://github.com/protocolbuffers/protobuf/releases/download/v${PROTOC_VERSION}/protoc-${PROTOC_VERSION}-linux-x86_64.zip -o protoc.zip
unzip -o protoc.zip -d /usr/local
rm -f protoc.zip

exit 0
