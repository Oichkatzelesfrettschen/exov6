#!/usr/bin/env bash
set -e

sudo apt-get update -y

sudo apt-get install -y \
  build-essential=12.9~deb12u1 \
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

# provide gmake alias if absent
if ! command -v gmake >/dev/null 2>&1; then
  sudo ln -sf $(which make) /usr/local/bin/gmake
fi

curl -fsSL https://raw.githubusercontent.com/protocolbuffers/protobuf/v25.1/install.sh | bash -s -- --version v25.1

exit 0
