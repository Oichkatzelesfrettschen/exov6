#!/usr/bin/env bash
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "$0")" && pwd)"
# Detect basic network connectivity; many CI environments are offline
NETWORK_AVAILABLE=true
if ! timeout 5 curl -fsSL https://pypi.org/simple >/dev/null 2>&1; then
  NETWORK_AVAILABLE=false
  echo "Network unavailable, proceeding in offline mode" >&2
fi
FAIL_LOG=/var/log/setup_failures.log
: >"$FAIL_LOG"
export DEBIAN_FRONTEND=noninteractive

#— helper to pin to the repo’s exact version if it exists
pip_install(){
  pkg="$1"
  if [ "$NETWORK_AVAILABLE" = false ]; then
    return 0
  fi
  if ! pip3 install --no-cache-dir "$pkg" >/dev/null 2>&1; then
    echo "Warning: pip install $pkg failed" >&2
    echo "pip $pkg" >>"$FAIL_LOG"
  fi
}
apt_pin_install(){
  pkg="$1"
  if [ "$NETWORK_AVAILABLE" = false ]; then
    return 0
  fi
  ver=$(apt-cache show "$pkg" 2>/dev/null \
        | awk '/^Version:/{print $2; exit}')
  if [ -n "$ver" ]; then
    if ! apt-get install -y "${pkg}=${ver}"; then
      echo "Warning: apt-get install ${pkg}=${ver} failed" >&2
      echo "apt ${pkg}=${ver}" >>"$FAIL_LOG"
    fi
  else
    if ! apt-get install -y "$pkg"; then
      echo "Warning: apt-get install $pkg failed" >&2
      echo "apt $pkg" >>"$FAIL_LOG"
    fi
  fi

  # Fallback to pip for Python packages
  if ! dpkg -s "$pkg" >/dev/null 2>&1; then
    case "$pkg" in
      python3-*|pre-commit)
        pip_pkg="${pkg#python3-}"
        pip_install "$pip_pkg"
        ;;
    esac
  fi
}

#— enable foreign architectures for cross-compilation
for arch in i386 armel armhf arm64 riscv64 powerpc ppc64el ia64; do
  dpkg --add-architecture "$arch"
done

if [ "$NETWORK_AVAILABLE" = true ]; then
  apt-get update -y || {
    echo "Warning: apt-get update failed" >&2
    echo "apt update" >>"$FAIL_LOG"
  }
else
  echo "Skipping apt-get update due to offline mode" >&2
fi

#— core build tools, formatters, analysis, science libs
for pkg in \
  build-essential gcc g++ clang lld llvm \
  clang-format clang-tidy clangd clang-tools uncrustify astyle editorconfig shellcheck pre-commit \
  make bmake ninja-build cmake meson \
  autoconf automake libtool m4 gawk flex bison byacc \
  pkg-config file ca-certificates curl git unzip graphviz \
  libopenblas-dev liblapack-dev libeigen3-dev \
  strace ltrace linux-perf systemtap systemtap-sdt-dev crash \
  valgrind kcachegrind trace-cmd kernelshark \
  libasan6 libubsan1 likwid hwloc; do
  apt_pin_install "$pkg"
done

# Ensure meson is available even if the package was missing
if ! command -v meson >/dev/null 2>&1; then
  pip_install meson
fi


#— Python & deep-learning / MLOps
for pkg in \
  python3 python3-pip python3-dev python3-venv python3-wheel \
  python3-numpy python3-scipy python3-pandas \
  python3-matplotlib python3-scikit-learn \
  python3-torch python3-torchvision python3-torchaudio \
  python3-onnx python3-onnxruntime python3-configuredb; do
  apt_pin_install "$pkg"
done

for pip_pkg in \
  tensorflow-cpu jax jaxlib \
  tensorflow-model-optimization mlflow onnxruntime-tools \
  black flake8 pyperf py-cpuinfo pytest pre-commit compile-db configuredb; do
  pip_install "$pip_pkg"
done

# Explicit installation of key tools
pip_install pre-commit
pip_install compile-db

# Fallback to pip if pre-commit is still missing
if ! command -v pre-commit >/dev/null 2>&1; then
  pip_install pre-commit || true
  if ! command -v pre-commit >/dev/null 2>&1; then
    cat <<'EOF' >/usr/local/bin/pre-commit
#!/usr/bin/env bash
echo "pre-commit not available in this environment" >&2
exit 1
EOF
    chmod +x /usr/local/bin/pre-commit
  fi
fi

if ! command -v pytest >/dev/null 2>&1; then
  pip_install pytest || true
fi

if ! command -v compiledb >/dev/null 2>&1; then
  pip_install compiledb || true
  if ! command -v compiledb >/dev/null 2>&1 && [ -f "$REPO_ROOT/scripts/gen_compile_commands.py" ]; then
    install -m755 "$REPO_ROOT/scripts/gen_compile_commands.py" /usr/local/bin/compiledb
  fi
fi

if ! command -v compile-db >/dev/null 2>&1; then
  pip_install compile-db || true
fi

#— QEMU emulation for foreign binaries
for pkg in \
  qemu-user-static \
  qemu-system-x86 qemu-system-arm qemu-system-aarch64 \
  qemu-system-riscv64 qemu-system-ppc qemu-system-ppc64 qemu-utils; do
  apt_pin_install "$pkg"
done

#— multi-arch cross-compilers
for pkg in \
  bcc bin86 elks-libc \
  gcc-multilib g++-multilib \
  binutils-i686-linux-gnu binutils-x86-64-linux-gnu \
  gcc-x86-64-linux-gnu g++-x86-64-linux-gnu \
  gcc-ia64-linux-gnu g++-ia64-linux-gnu \
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
  gcc-loongarch64-linux-gnu g++-loongarch64-linux-gnu \
  gcc-mips-linux-gnu g++-mips-linux-gnu \
  gcc-mipsel-linux-gnu g++-mipsel-linux-gnu \
  gcc-mips64-linux-gnuabi64 g++-mips64-linux-gnuabi64 \
  gcc-mips64el-linux-gnuabi64 g++-mips64el-linux-gnuabi64; do
  apt_pin_install "$pkg"
done

#— bare-metal ELF cross-compilers
for pkg in \
  gcc-i386-elf g++-i386-elf \
  gcc-x86-64-elf g++-x86-64-elf; do
  apt_pin_install "$pkg"
done

#— high-level language runtimes and tools
for pkg in \
  golang-go nodejs npm typescript \
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
  r-base r-base-dev dart flutter gnat gprbuild gfortran gnucobol \
  fpc lazarus zig nim nimble crystal shards gforth; do
  apt_pin_install "$pkg"
done

#— GUI & desktop-dev frameworks
for pkg in \
  libqt5-dev qtcreator libqt6-dev \
  libgtk1.2-dev libgtk2.0-dev libgtk-3-dev libgtk-4-dev \
  libfltk1.3-dev xorg-dev libx11-dev libxext-dev \
  libmotif-dev openmotif cde \
  xfce4-dev-tools libxfce4ui-2-dev lxde-core lxqt-dev-tools \
  libefl-dev libeina-dev \
  libwxgtk3.0-dev libwxgtk3.0-gtk3-dev \
  libsdl2-dev libsdl2-image-dev libsdl2-ttf-dev \
  libglfw3-dev libglew-dev; do
  apt_pin_install "$pkg"
done

#— containers, virtualization, HPC, debug
for pkg in \
  docker.io podman buildah virt-manager libvirt-daemon-system qemu-kvm \
  bochs bochs-sdl \
  gdb lldb perf gcovr lcov bcc-tools bpftrace \
  openmpi-bin libopenmpi-dev mpich; do
  apt_pin_install "$pkg"
done
# Ensure swiftc is available; install official Swift toolchain if missing
if ! command -v swiftc >/dev/null 2>&1; then
  echo "swiftc not found, fetching official Swift toolchain" >&2
  ARCH=$(uname -m)
  OS_VERSION=$(. /etc/os-release; echo ${VERSION_ID})
  SWIFT_VERSION=5.9.2
  PLATFORM="ubuntu${OS_VERSION}"
  case "$ARCH" in
    x86_64|amd64)
      SWIFT_FILE="swift-${SWIFT_VERSION}-RELEASE-${PLATFORM}.tar.gz"
      ;;
    aarch64|arm64)
      SWIFT_FILE="swift-${SWIFT_VERSION}-RELEASE-${PLATFORM}-aarch64.tar.gz"
      ;;
    *)
      echo "Unsupported architecture: $ARCH" >&2
      SWIFT_FILE="swift-${SWIFT_VERSION}-RELEASE-${PLATFORM}.tar.gz"
      ;;
  esac
  BASE_URL="https://download.swift.org/swift-${SWIFT_VERSION}-release/${PLATFORM}"
  mkdir -p /opt/swift
  curl -fsSL "${BASE_URL}/${SWIFT_FILE}" -o /tmp/swift.tar.gz
  tar -xzf /tmp/swift.tar.gz -C /opt/swift --strip-components=1
  rm /tmp/swift.tar.gz
  echo 'export PATH=/opt/swift/usr/bin:$PATH' > /etc/profile.d/swift.sh
  export PATH=/opt/swift/usr/bin:$PATH
fi

swiftc --version || true

#— ISA optimization and benchmarking tools
for pkg in \
  nasm yasm cpuid msr-tools numactl oprofile libpfm4-dev; do
  apt_pin_install "$pkg"
done
# Ensure swiftc is available; install official Swift toolchain if missing
if ! command -v swiftc >/dev/null 2>&1; then
  echo "swiftc not found, fetching official Swift toolchain" >&2
  ARCH=$(uname -m)
  OS_VERSION=$(. /etc/os-release; echo ${VERSION_ID})
  SWIFT_VERSION=5.9.2
  PLATFORM="ubuntu${OS_VERSION}"
  case "$ARCH" in
    x86_64|amd64)
      SWIFT_FILE="swift-${SWIFT_VERSION}-RELEASE-${PLATFORM}.tar.gz"
      ;;
    aarch64|arm64)
      SWIFT_FILE="swift-${SWIFT_VERSION}-RELEASE-${PLATFORM}-aarch64.tar.gz"
      ;;
    *)
      echo "Unsupported architecture: $ARCH" >&2
      SWIFT_FILE="swift-${SWIFT_VERSION}-RELEASE-${PLATFORM}.tar.gz"
      ;;
  esac
  BASE_URL="https://download.swift.org/swift-${SWIFT_VERSION}-release/${PLATFORM}"
  mkdir -p /opt/swift
  if ! curl -fsSL "${BASE_URL}/${SWIFT_FILE}" -o /tmp/swift.tar.gz; then
    echo "Warning: failed to download Swift toolchain" >&2
    echo "download swift" >>"$FAIL_LOG"
  else
    tar -xzf /tmp/swift.tar.gz -C /opt/swift --strip-components=1 || {
      echo "Warning: extracting Swift toolchain failed" >&2
      echo "extract swift" >>"$FAIL_LOG"
    }
    rm /tmp/swift.tar.gz
  fi
  echo 'export PATH=/opt/swift/usr/bin:$PATH' > /etc/profile.d/swift.sh
  export PATH=/opt/swift/usr/bin:$PATH
fi

swiftc --version || true

#— IA-16 (8086/286) cross-compiler
IA16_VER=$(curl -fsSL https://api.github.com/repos/tkchia/gcc-ia16/releases/latest \
           | awk -F\" '/tag_name/{print $4; exit}')
if ! curl -fsSL "https://github.com/tkchia/gcc-ia16/releases/download/${IA16_VER}/ia16-elf-gcc-linux64.tar.xz" \
  | tar -Jx -C /opt; then
  echo "Warning: failed to install IA16 cross compiler" >&2
  echo "download ia16" >>"$FAIL_LOG"
fi
echo 'export PATH=/opt/ia16-elf-gcc/bin:$PATH' > /etc/profile.d/ia16.sh
export PATH=/opt/ia16-elf-gcc/bin:$PATH

#— protoc installer (pinned)
PROTO_VERSION=25.1
if ! curl -fsSL "https://raw.githubusercontent.com/protocolbuffers/protobuf/v${PROTO_VERSION}/protoc-${PROTO_VERSION}-linux-x86_64.zip" \
  -o /tmp/protoc.zip; then
  echo "Warning: failed to download protoc" >&2
  echo "download protoc" >>"$FAIL_LOG"
else
  unzip -d /usr/local /tmp/protoc.zip || {
    echo "Warning: failed to unzip protoc" >&2
    echo "unzip protoc" >>"$FAIL_LOG"
  }
  rm /tmp/protoc.zip
fi

#— gmake alias
command -v gmake >/dev/null 2>&1 || ln -s "$(command -v make)" /usr/local/bin/gmake

# Generate compile_commands.json if compiledb is installed
if command -v compiledb >/dev/null 2>&1; then
  status=0
  compiledb -n make >/dev/null || status=$?
  if [ $status -ne 0 ] || [ ! -f compile_commands.json ]; then
    echo "Warning: failed to generate compile_commands.json (exit code $status)" >&2
    echo "compiledb" >>"$FAIL_LOG"
  fi
elif [ -x scripts/gen_compile_commands.py ]; then
  if ! python3 scripts/gen_compile_commands.py >/dev/null 2>&1; then
    echo "Warning: gen_compile_commands.py failed" >&2
    echo "gen_compile_commands" >>"$FAIL_LOG"
  fi
fi

# Install pre-commit hooks if possible
if command -v pre-commit >/dev/null 2>&1; then
  if ! pre-commit install >/dev/null 2>&1; then
    echo "Warning: pre-commit install failed" >&2
    echo "pre-commit install" >>"$FAIL_LOG"
  fi
fi

#— clean up
apt-get clean
rm -rf /var/lib/apt/lists/*

exit 0
