#!/usr/bin/env bash
set -euo pipefail
export DEBIAN_FRONTEND=noninteractive

# Helper to install exact repo versions when available
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

# Enable foreign architectures for cross-compilers
for arch in i386 armel armhf arm64 riscv64 powerpc ppc64el ia64 m68k hppa loongarch64; do
  dpkg --add-architecture "$arch"
done

apt-get -o Acquire::Retries=3 -o Acquire::http::Timeout=15 update

# Core build tools and libraries
CORE_PKGS=(
  build-essential gcc g++ clang lld llvm
  clang-format uncrustify astyle editorconfig pre-commit
  make bmake ninja-build cmake meson
  autoconf automake libtool m4 gawk flex bison byacc
  pkg-config file ca-certificates curl git unzip
  libopenblas-dev liblapack-dev libeigen3-dev
  linux-headers-amd64 bc kmod fakeroot
  strace ltrace linux-perf systemtap systemtap-sdt-dev crash
  valgrind kcachegrind trace-cmd kernelshark
  libasan6 libubsan1 likwid hwloc
)

for pkg in "${CORE_PKGS[@]}"; do
  apt_pin_install "$pkg"
done

# Python and ML stack
PY_PKGS=(
  python3 python3-pip python3-dev python3-venv python3-wheel
  python3-numpy python3-scipy python3-pandas
  python3-matplotlib python3-scikit-learn
  python3-torch python3-torchvision python3-torchaudio
  python3-onnx python3-onnxruntime
)

for pkg in "${PY_PKGS[@]}"; do
  apt_pin_install "$pkg"
done

pip3 install --no-cache-dir tensorflow-cpu jax jaxlib \
  tensorflow-model-optimization mlflow onnxruntime-tools

# QEMU emulators
QEMU_PKGS=(
  qemu-user-static
  qemu-system-x86 qemu-system-arm qemu-system-aarch64
  qemu-system-riscv64 qemu-system-ppc qemu-system-ppc64 qemu-utils
)
for pkg in "${QEMU_PKGS[@]}"; do
  apt_pin_install "$pkg"
done

# Cross-compilers
CROSS_PKGS=(
  bcc bin86 elks-libc
  gcc-ia64-linux-gnu g++-ia64-linux-gnu
  gcc-i686-linux-gnu g++-i686-linux-gnu
  gcc-aarch64-linux-gnu g++-aarch64-linux-gnu
  gcc-arm-linux-gnueabi g++-arm-linux-gnueabi
  gcc-arm-linux-gnueabihf g++-arm-linux-gnueabihf
  gcc-riscv64-linux-gnu g++-riscv64-linux-gnu
  gcc-powerpc-linux-gnu g++-powerpc-linux-gnu
  gcc-powerpc64-linux-gnu g++-powerpc64-linux-gnu
  gcc-powerpc64le-linux-gnu g++-powerpc64le-linux-gnu
  gcc-m68k-linux-gnu g++-m68k-linux-gnu
  gcc-hppa-linux-gnu g++-hppa-linux-gnu
  gcc-loongarch64-linux-gnu g++-loongarch64-linux-gnu
  gcc-mips-linux-gnu g++-mips-linux-gnu
  gcc-mipsel-linux-gnu g++-mipsel-linux-gnu
  gcc-mips64-linux-gnuabi64 g++-mips64-linux-gnuabi64
  gcc-mips64el-linux-gnuabi64 g++-mips64el-linux-gnuabi64
)
for pkg in "${CROSS_PKGS[@]}"; do
  apt_pin_install "$pkg"
done

# High-level languages and tooling
LANG_PKGS=(
  golang-go
  nodejs npm typescript
  rustc cargo clippy rustfmt
  lua5.4 liblua5.4-dev luarocks
  ghc cabal-install haskell-stack alex happy hlint stylish-haskell haskell-doc
  sbcl ecl clisp cl-quicklisp slime cl-asdf common-lisp-hyperspec
  ldc gdc dmd-compiler dub libphobos-dev
  chicken-bin libchicken-dev chicken-doc
  openjdk-17-jdk maven gradle dotnet-sdk-8 mono-complete
  swift swift-lldb swiftpm kotlin gradle-plugin-kotlin
  ruby ruby-dev gem bundler
  php-cli php-dev composer phpunit
  r-base r-base-dev
  dart flutter
  gfortran gnat gprbuild gnucobol fpc lazarus
  zig nim nimble crystal shards gforth
)
for pkg in "${LANG_PKGS[@]}"; do
  apt_pin_install "$pkg"
done

# GUI and desktop frameworks
GUI_PKGS=(
  libqt5-dev qtcreator libqt6-dev
  libgtk1.2-dev libgtk2.0-dev libgtk-3-dev libgtk-4-dev
  libfltk1.3-dev xorg-dev libx11-dev libxext-dev
  libmotif-dev openmotif cde
  xfce4-dev-tools libxfce4ui-2-dev lxde-core lxqt-dev-tools
  libefl-dev libeina-dev
  libwxgtk3.0-dev libwxgtk3.0-gtk3-dev
  libsdl2-dev libsdl2-image-dev libsdl2-ttf-dev
  libglfw3-dev libglew-dev
)
for pkg in "${GUI_PKGS[@]}"; do
  apt_pin_install "$pkg"
done

# Containers, virtualization, debugging, coverage, MPI
MISC_PKGS=(
  docker.io podman buildah virt-manager libvirt-daemon-system qemu-kvm
  gdb lldb perf gcovr lcov bcc-tools bpftrace
  openmpi-bin libopenmpi-dev mpich
)
for pkg in "${MISC_PKGS[@]}"; do
  apt_pin_install "$pkg"
done

# IA-16 GCC
IA16_VER=$(curl -fsSL https://api.github.com/repos/tkchia/gcc-ia16/releases/latest | awk -F\" '/tag_name/{print $4; exit}')
curl -fsSL "https://github.com/tkchia/gcc-ia16/releases/download/${IA16_VER}/ia16-elf-gcc-linux64.tar.xz" | tar -Jx -C /opt
echo 'export PATH=/opt/ia16-elf-gcc/bin:$PATH' > /etc/profile.d/ia16.sh
export PATH=/opt/ia16-elf-gcc/bin:$PATH

# Install protoc
PROTO_VERSION=25.1
curl -fsSL "https://raw.githubusercontent.com/protocolbuffers/protobuf/v${PROTO_VERSION}/protoc-${PROTO_VERSION}-linux-x86_64.zip" -o /tmp/protoc.zip
unzip -d /usr/local /tmp/protoc.zip
rm /tmp/protoc.zip

# Provide gmake if absent
command -v gmake >/dev/null 2>&1 || ln -s "$(command -v make)" /usr/local/bin/gmake

apt-get clean
rm -rf /var/lib/apt/lists/*

exit 0
