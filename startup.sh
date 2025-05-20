#!/usr/bin/env bash
###############################################################################
# Codex Cloud "everything + x86_64 + Eigen + ML + kernel dev" bootstrap
# Generated: 20-May-2025
###############################################################################
set -Eeuo pipefail
export DEBIAN_FRONTEND=noninteractive

# 0. Enable multi-arch for runtime libs
for arch in i386 armel armhf arm64 riscv64 powerpc ppc64el ia64; do
  dpkg --add-architecture "$arch"
done
apt-get -o Acquire::Retries=3 -o Acquire::http::Timeout=15 update

# 1. Core system, math libs, kernel dev, build helpers
apt-get install -y --no-install-recommends \
  ca-certificates curl git file pkg-config \
  flex bison byacc gawk \
  libelf-dev libncurses5-dev libssl-dev libexpat1-dev \
  python3 python3-pip \
  libopenblas-dev liblapack-dev libeigen3-dev \
  linux-headers-amd64 bc kmod fakeroot \
  build-essential gcc g++ gcc-multilib g++-multilib \
  gcc-x86-64-linux-gnu g++-x86-64-linux-gnu \
  clang lld llvm clang-tidy clang-tools cppcheck \
  cmake make bmake ninja-build meson autoconf automake libtool m4 \
  binfmt-support \
  unzip

# Provide gmake alias for scripts expecting it
command -v gmake >/dev/null 2>&1 || ln -s "$(command -v make)" /usr/local/bin/gmake

# 2. Extended Python ML & data stack
apt-get install -y --no-install-recommends \
  python3-numpy python3-scipy python3-pandas \
  python3-matplotlib python3-scikit-learn \
  python3-dev python3-venv python3-wheel

# 3. Extended languages & tooling
apt-get install -y --no-install-recommends \
  rustc cargo clippy rustfmt \
  lua5.4 liblua5.4-dev luarocks \
  ghc cabal-install \
  sbcl chicken-bin guile-3.0 \
  fish zsh zsh-syntax-highlighting

# 4. Cross-compilers (IA-16 thru 64-bit + ARM + RISC-V + PPC)
apt-get install -y --no-install-recommends \
  bcc bin86 elks-libc \
  gcc-ia64-linux-gnu g++-ia64-linux-gnu \
  gcc-i686-linux-gnu g++-i686-linux-gnu \
  gcc-arm-linux-gnueabi g++-arm-linux-gnueabi \
  gcc-arm-linux-gnueabihf g++-arm-linux-gnueabihf \
  gcc-aarch64-linux-gnu g++-aarch64-linux-gnu \
  gcc-riscv64-linux-gnu g++-riscv64-linux-gnu \
  gcc-powerpc-linux-gnu g++-powerpc-linux-gnu \
  gcc-powerpc64-linux-gnu g++-powerpc64-linux-gnu \
  gcc-powerpc64le-linux-gnu g++-powerpc64le-linux-gnu

# 5. QEMU user-mode & system emulators
apt-get install -y --no-install-recommends \
  qemu-user-static \
  qemu-system-x86 qemu-system-arm qemu-system-aarch64 \
  qemu-system-riscv64 qemu-system-ppc qemu-system-ppc64 qemu-utils

# 6. IA-16 GCC (modern) via tkchia/gcc-ia16
IA16_VER=$(curl -s https://api.github.com/repos/tkchia/gcc-ia16/releases/latest \
           | grep '"tag_name":' | cut -d" -f4)
curl -L "https://github.com/tkchia/gcc-ia16/releases/download/${IA16_VER}/ia16-elf-gcc-linux64.tar.xz" \
  | tar -Jx -C /opt
echo 'export PATH=/opt/ia16-elf-gcc/bin:$PATH' > /etc/profile.d/ia16.sh
export PATH=/opt/ia16-elf-gcc/bin:$PATH

# 7. (Opt) Latest CMake binary for fastest performance
LATEST_CMAKE=$(curl -s https://api.github.com/repos/Kitware/CMake/releases/latest \
               | grep '"tag_name":' | cut -d" -f4 | tr -d v)
curl -L "https://github.com/Kitware/CMake/releases/download/v${LATEST_CMAKE}/cmake-${LATEST_CMAKE}-linux-x86_64.tar.gz" \
  | tar --strip-components=1 -xz -C /usr/local

# 8. Export project languages & asm targets
cat << 'EOL' > /etc/profile.d/project-languages.sh
export PROJECT_LANG_PRIMARY="C23"
export PROJECT_ASM_SHARED="asm/primitives"
export PROJECT_ASM_IA16="arch/ia16"
export PROJECT_ASM_IA32="arch/ia32"
export PROJECT_ASM_IA64="arch/ia64"
export PROJECT_ASM_PPC64="arch/ppc64"
export PROJECT_ASM_PPC64LE="arch/ppc64le"
export PROJECT_LANG_RUST="rust"
export PROJECT_LANG_LUA="lua5.4"
export PROJECT_LANG_HASKELL="ghc"
export PROJECT_LANG_LISP=('sbcl' 'chicken' 'guile')
export PROJECT_SHELLS=('bash' 'zsh' 'fish')
EOL

# 9. Final clean-up
apt-get clean
rm -rf /var/lib/apt/lists/*

echo " Fully refined maximal setup complete."
