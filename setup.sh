#!/bin/bash
set -e

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

apt-get update || true

apt_pin_install build-essential
apt_pin_install gcc
apt_pin_install g++
apt_pin_install clang
apt_pin_install clang-format
apt_pin_install gdb
apt_pin_install qemu-system-x86
apt_pin_install qemu-utils
apt_pin_install make
apt_pin_install cmake
apt_pin_install bmake
apt_pin_install nasm
apt_pin_install python3
apt_pin_install python3-pip
apt_pin_install golang
apt_pin_install nodejs
apt_pin_install npm
apt_pin_install rustc
apt_pin_install cargo
apt_pin_install curl
apt_pin_install bash

curl -fsSL https://example.com/protoc-install.sh | bash

exit 0

