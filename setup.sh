#!/ usr / bin / env bash
set - euo pipefail

#Optional debugging mode.Use-- debug to enable verbose tracing.
          DEBUG_MODE = false

#simple debug logger
    debug() {
  if
    ["$DEBUG_MODE" = true];
  then echo "[DEBUG] $*" > &2 fi
}

REPO_ROOT = "$(cd " $(dirname "$0") " && pwd)"
#This script installs all build dependencies.It logs actions to
#/ var / log /                                                                 \
    setup.log and records any failures in / var / log / setup_failures.log.
#After the initial installation attempt it retries failed packages once using
#apt, pip or npm depending on the recorded method.

#Parse command line arguments
    OFFLINE_MODE = false while[$ # - gt 0];
do
  case "$1" in
    --offline)
      OFFLINE_MODE=true
      ;;
    --debug)
      DEBUG_MODE=true
      ;;
    *)
      echo "Usage: $0 [--offline] [--debug]" >&2
      exit 1
      ;;
  esac
  shift
done

if [ "$DEBUG_MODE" = true ]; then
  set -x
fi

#In offline mode or when network is unavailable the script attempts
#to install packages from the scripts / offline_packages directory.Ensure this
#directory is populated with the required.deb files or Python wheels
#as described in scripts / offline_packages /                                \
      README.md.Otherwise most installs
#will be skipped and logged as warnings.

#Detect basic network connectivity unless offline mode was requested
NETWORK_AVAILABLE=true
if [ "$OFFLINE_MODE" = true ]; then
  NETWORK_AVAILABLE=false
  echo "Offline mode enabled" >&2
elif ! timeout 5 curl -fsSL https://pypi.org/simple >/dev/null 2>&1; then
    NETWORK_AVAILABLE =
        false echo
        "Network unavailable, proceeding in offline mode" > & 2 fi LOG_FILE =
            / var / log /
            setup.log FAIL_LOG = / var / log / setup_failures.log mkdir -
                                     p / var / log : >
                                                     "$LOG_FILE"
        : > "$FAIL_LOG" exec >>
          (tee - a "$LOG_FILE")2 > & 1 export DEBIAN_FRONTEND = noninteractive

#— helper to pin to the repo’s exact version if it exists
        pip_install() {
      pkg = "$1" debug "Attempting pip install $pkg" if !pip3 install-- no -
                cache - dir "$pkg" >
            / dev / null 2 > &1;
      then echo "Warning: pip install $pkg failed" > &2 echo "pip $pkg" >>
          "$FAIL_LOG" fi
    }
  apt_pin_install() {
    pkg = "$1" debug
          "Attempting apt install $pkg" if["$NETWORK_AVAILABLE" != true];
    then echo "Warning: network unavailable, skipping apt-get install of $pkg" >
            & 2 return 0 fi

                status = 0 ver = $(apt - cache show "$pkg" 2 > / dev / null |
                                       awk '/^Version:/{print $2; exit}' ||
                                   true) if[-n "$ver"];
    then if !apt - get install - y "${pkg}=${ver}";
    then echo "Warning: apt-get install ${pkg}=${ver} failed" >
        &2 echo "apt ${pkg}=${ver}" >>
        "$FAIL_LOG" status = 1 fi else if !apt - get install - y "$pkg";
    then echo "Warning: apt-get install $pkg failed" > &2 echo "apt $pkg" >>
        "$FAIL_LOG" status = 1 fi fi

                                 if !dpkg -
                                 s "$pkg" >
                             / dev / null 2 > &1; then
    case "$pkg" in
      python3-*)
        pip_pkg="${pkg#python3-}"
        pip_install "$pip_pkg"
        if command -v "$pip_pkg" >/dev/null 2>&1 || \
           python3 -c "import $pip_pkg" >/dev/null 2>&1; then
          status=0
        fi
        ;;
    esac
  fi

  if [ $status -ne 0 ] && ! command -v "$pkg" >/dev/null 2>&1; then
    if command -v npm >/dev/null 2>&1; then
      debug "Attempting npm install $pkg"
      if ! npm install -g "$pkg" >/dev/null 2>&1; then
        echo "Warning: npm install $pkg failed" >&2
        echo "npm $pkg" >>"$FAIL_LOG"
      else
        status=0
      fi
    fi
  fi

  if [ $status -ne 0 ]; then
    case "$pkg" in
      capnproto|capnp*)
        if ! command -v capnp >/dev/null 2>&1; then
          if ! curl -fsSL https://capnproto.org/capnproto-c++-1.0.1.tar.gz \
              -o /tmp/capnp.tar.gz; then
    echo "Warning: failed to download capnproto" >
            &2 echo "download capnproto" >>
            "$FAIL_LOG" else tar - xzf / tmp / capnp.tar.gz -
                C / tmp(cd / tmp / capnproto - *&&./ configure &&
                        make - j "$(nproc)" && make install) ||
        {echo "Warning: building capnproto failed" >
         &2 echo "build capnproto" >> "$FAIL_LOG"} rm -
            rf / tmp / capnproto - */ tmp / capnp.tar.gz fi fi;
    ;
    esac fi

        return 0
  }

#ensure_command tries to install specified packages until the command exists.
#Missing commands are logged but do not halt the script.
  ensure_command() {
    local cmd = "$1" shift if command - v "$cmd" > / dev / null 2 > &1; then
    return 0
  fi
  local pkg
  for pkg in "$@";
    do
      apt_pin_install "$pkg" done if !command - v "$cmd" > / dev / null 2 > &1;
    then echo
        "Warning: required command $cmd not found after install attempts" >
        &2 echo "missing $cmd" >> "$FAIL_LOG" fi
  }

#Install packages from scripts / offline_packages /                          \
      when network is unavailable
  install_offline_packages() {
    dir = "$REPO_ROOT/scripts/offline_packages" if[-d "$dir"]; then
    shopt -s nullglob
    files=("$dir"/*.deb)
    if [ ${#files[@]} -eq 0 ]; then
      echo "Warning: no offline packages found in $dir" >&2
    fi
    for deb in "${files[@]}"; do
      if ! dpkg -i "$deb"; then
        echo "Warning: dpkg -i $deb failed" >&2
        echo "dpkg $deb" >>"$FAIL_LOG"
      fi
    done
    shopt -u nullglob
  else
    echo "Warning: scripts/offline_packages directory not found" >&2
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
  if ! apt-get dist-upgrade -y; then
    echo "Warning: apt-get dist-upgrade failed" >&2
    echo "apt dist-upgrade" >>"$FAIL_LOG"
  fi
else
  echo "Skipping apt-get update due to offline mode" >&2
fi

if [ "$NETWORK_AVAILABLE" != true ]; then
  install_offline_packages
fi

# Default optimization and linker settings
export CC=${CC:-"ccache clang"}
export CXX=${CXX:-"ccache clang++"}
export CFLAGS="${CFLAGS:--O3 -pipe -march=native}"
export CXXFLAGS="${CXXFLAGS:--O3 -pipe -march=native}"
export LDFLAGS="${LDFLAGS:--fuse-ld=lld}"
export MAKEFLAGS="${MAKEFLAGS:--j$(nproc)}"

#— core build tools, formatters, analysis, science libs
# The project now builds primarily with clang.  GCC packages remain only
# for cross-compilers and legacy support.
for pkg in \
  build-essential gcc g++ g++-13 clang clang-16 lld llvm llvm-bolt \
  clang-format clang-tidy clangd clang-tools ccache uncrustify astyle editorconfig \
  make bmake ninja-build cmake meson \
  autoconf automake libtool m4 gawk flex bison byacc \
  pkg-config file ca-certificates curl git unzip graphviz doxygen doxygen-latex \
  libopenblas-dev liblapack-dev libeigen3-dev \
  strace ltrace linux-perf systemtap systemtap-sdt-dev crash \
  valgrind kcachegrind trace-cmd kernelshark \
  libasan6 libubsan1 likwid hwloc cloc; do
  apt_pin_install "$pkg"
done

# Ensure meson is available even if the package was missing
if ! command -v meson >/dev/null 2>&1; then
  pip_install meson
fi


#— Python tooling
for pkg in \
  python3 python3-pip python3-dev python3-venv python3-wheel \
  python3-sphinx python3-sphinx-rtd-theme; do
  apt_pin_install "$pkg"
done

for pip_pkg in \
  black flake8 pyperf py-cpuinfo pytest compiledb configuredb \
  pyyaml pylint pyfuzz; do
  pip_install "$pip_pkg"
done

# Explicit installation of key tools
pip_install compiledb
pip_install configuredb



if ! command -v pytest >/dev/null 2>&1; then
  pip_install pytest || true
fi
pytest --version || true

if ! command -v compiledb >/dev/null 2>&1; then
  pip_install compiledb || true
  pip_install compile-db || true
  if ! command -v compiledb >/dev/null 2>&1 && [ -f "$REPO_ROOT/scripts/gen_compile_commands.py" ]; then
    install -m755 "$REPO_ROOT/scripts/gen_compile_commands.py" /usr/local/bin/compiledb
  fi
  if ! command -v compiledb >/dev/null 2>&1; then
    cat <<'EOF' >/usr/local/bin/compiledb
#!/usr/bin/env bash
echo "compiledb not available in this environment" >&2
exit 1
EOF
    chmod +x /usr/local/bin/compiledb
  fi
fi

if ! command -v compile-db >/dev/null 2>&1 && command -v compiledb >/dev/null 2>&1; then
  ln -s "$(command -v compiledb)" /usr/local/bin/compile-db 2>/dev/null || true
elif ! command -v compile-db >/dev/null 2>&1; then
  pip_install compile-db || true
  if ! command -v compile-db >/dev/null 2>&1; then
    cat <<'EOF' >/usr/local/bin/compile-db
#!/usr/bin/env bash
echo "compile-db not available in this environment" >&2
exit 1
EOF
    chmod +x /usr/local/bin/compile-db
  fi
fi

if ! command -v configuredb >/dev/null 2>&1; then
  pip_install configuredb || true
  if ! command -v configuredb >/dev/null 2>&1; then
    cat <<'EOF' >/usr/local/bin/configuredb
#!/usr/bin/env bash
echo "configuredb not available in this environment" >&2
exit 1
EOF
    chmod +x /usr/local/bin/configuredb
  fi
fi

# Ensure additional Python tooling is installed
for tool in pylint pyfuzz; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    pip_install "$tool" || true
  fi
done

python3 - <<'EOF' || true
import yaml
yaml.safe_load("key: value")
EOF

if ! command -v configuredb >/dev/null 2>&1; then
  pip_install configuredb || true
fi
configuredb --help >/dev/null 2>&1 || true

#— QEMU emulation for foreign binaries
for pkg in \
  qemu-user-static \
  qemu-system-x86 qemu-system-arm qemu-system-aarch64 \
  qemu-system-riscv64 qemu-system-ppc qemu-system-ppc64 qemu-utils qemu-nox; do
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
  r-base r-base-dev dart flutter gnat gprbuild gfortran gnucobol \
  fpc lazarus zig nim nimble crystal shards gforth \
  nodejs npm \
  coq coqide coq-theories tlaplus; do
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
  bochs bochs-sdl tmux \
  gdb lldb perf gcovr lcov bcc-tools bpftrace \
  openmpi-bin libopenmpi-dev mpich; do
  apt_pin_install "$pkg"
done

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

# Verify the host compiler supports the C2X standard used by standalone tests
cc_cmd=""
if command -v clang >/dev/null 2>&1; then
  cc_cmd=clang
elif command -v gcc >/dev/null 2>&1; then
  cc_cmd=gcc
fi
if [ -n "$cc_cmd" ]; then
  if ! echo 'int main(void){return 0;}' | $cc_cmd -std=c2x -x c - \
      -o /tmp/c2x_test >/dev/null 2>&1; then
    echo "Error: $cc_cmd lacks -std=c2x support which is required for some tests" >&2
    echo "$cc_cmd no c2x" >>"$FAIL_LOG"
  fi
  rm -f /tmp/c2x_test
fi

# Ensure critical tools are installed
ensure_command clang clang clang-16
ensure_command clang-tidy clang-tidy
ensure_command clang-format clang-format
ensure_command meson meson
ensure_command coqc coq coqide coq-theories
ensure_command tlc tlaplus

# Check for essential commands and log if any are missing
for cmd in clang clang++ cmake qemu-system-x86 qemu-nox tmux cloc coqc; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "Warning: required command $cmd not found" >&2
    echo "missing $cmd" >>"$FAIL_LOG"
  fi
done


#— clean up
apt-get clean
rm -rf /var/lib/apt/lists/*

# Retry failed installations once using the recorded failure log. This helps
# resolve transient network issues or missing dependencies and documents each
# attempt in $FAIL_LOG for future troubleshooting.
if [ -s "$FAIL_LOG" ]; then
  echo "Retrying failed package installations" >&2
  mapfile -t _fails <"$FAIL_LOG"
  : >"$FAIL_LOG"
  for entry in "${_fails[@]}"; do
    set -- $entry
    method=$1
    pkg=${entry#"$method "}
    case "$method" in
      apt)
        apt_pin_install "$pkg" || echo "$entry" >>"$FAIL_LOG"
        ;;
      pip)
        pip_install "$pkg" || echo "$entry" >>"$FAIL_LOG"
        ;;
      npm)
        if command -v npm >/dev/null 2>&1; then
          npm install -g "$pkg" >/dev/null 2>&1 || echo "$entry" >>"$FAIL_LOG"
        else
          echo "$entry" >>"$FAIL_LOG"
        fi
        ;;
      *)
        echo "$entry" >>"$FAIL_LOG"
        ;;
    esac
  done
fi

if [ -s "$FAIL_LOG" ]; then
  echo "Setup completed with warnings. Review $FAIL_LOG for details." >&2
else
  echo "Setup completed successfully." >&2
fi

exit 0
