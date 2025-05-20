#!/usr/bin/env bash
set -euo pipefail

# Pin specific tool versions
GCC_VERSION=13
CLANG_VERSION=16
CMAKE_VERSION=3.28
NODE_VERSION=20
RUST_VERSION=1.73.0
PROTOC_VERSION=24.4

export DEBIAN_FRONTEND=noninteractive

# Update package lists
apt-get update

# Enable NodeSource for a pinned Node version
curl -fsSL "https://deb.nodesource.com/setup_${NODE_VERSION}.x" | bash -

# Base build tools
apt-get install -y --no-install-recommends \
    build-essential="4:$GCC_VERSION.*" \
    gcc-$GCC_VERSION g++-$GCC_VERSION \
    gcc-x86-64-linux-gnu="4:$GCC_VERSION.*" \
    g++-x86-64-linux-gnu="4:$GCC_VERSION.*" \
    gcc-aarch64-linux-gnu="4:$GCC_VERSION.*" \
    g++-aarch64-linux-gnu="4:$GCC_VERSION.*" \
    clang-$CLANG_VERSION \
    cmake=$CMAKE_VERSION* \
    make bmake \
    nasm \
    python3 python3-pip \
    golang-go \
    rustc=$RUST_VERSION* cargo=$RUST_VERSION* \
    nodejs=$NODE_VERSION* npm=$NODE_VERSION* \
    qemu-system-x86 qemu-system-aarch64 qemu-utils \
    curl unzip

# Provide gmake symlink for environments that expect it
ln -sf "$(command -v make)" /usr/local/bin/gmake

# Install protoc from release archive
cd /tmp
curl -sSL "https://github.com/protocolbuffers/protobuf/releases/download/v${PROTOC_VERSION}/protoc-${PROTOC_VERSION}-linux-x86_64.zip" -o protoc.zip
unzip protoc.zip -d /usr/local
rm protoc.zip

exit 0
