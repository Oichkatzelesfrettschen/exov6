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
