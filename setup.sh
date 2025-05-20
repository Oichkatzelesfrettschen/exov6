#!/usr/bin/env bash
set -euo pipefail

export DEBIAN_FRONTEND=noninteractive

apt_pin_install() {
  local pkg="$1"
  local ver
  ver=$(apt-cache show "$pkg" 2>/dev/null | awk '/^Version:/{print $2; exit}')
  if [ -n "$ver" ]; then
    apt-get install -y "${pkg}=${ver}"
  else
    apt-get install -y "$pkg"
  fi
}

apt-get update -y || true

packages=(
  build-essential
  gcc
  g++
  clang
  clang-format
  clang-tidy
  scan-build
  make
  bmake
  cmake
  ninja-build
  gcc-multilib
  g++-multilib
  qemu-system-x86
  qemu-utils
  nasm
  x86_64-elf-gcc
  x86_64-elf-binutils
  python3
  python3-pip
  golang-go
  nodejs
  npm
  rustc
  cargo
  curl
  git
  file
  pkg-config
)

for pkg in "${packages[@]}"; do
  apt_pin_install "$pkg"
done

command -v gmake >/dev/null 2>&1 || ln -s "$(command -v make)" /usr/local/bin/gmake

curl -fsSL https://raw.githubusercontent.com/protocolbuffers/protobuf/v25.1/install.sh | bash -s -- --version v25.1

exit 0
