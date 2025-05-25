#!/usr/bin/env bash
set -euo pipefail

# Build xv6 for multiple x86 CPU feature sets using CMake and Ninja.

ARCH=${ARCH:-x86_64}

# Map variant name -> CPUFLAGS
declare -A ISA_FLAGS=(
  [baseline]=""
  [x87]="-mfpmath=387"
  [mmx]="-mmmx"
  [sse]="-msse"
  [sse2]="-msse2"
  [sse3]="-msse3"
  [ssse3]="-mssse3"
  [sse4.1]="-msse4.1"
  [sse4.2]="-msse4.2"
  [avx]="-mavx"
  [avx2]="-mavx2"
  [fma]="-mfma"
  [avx512]="-mavx512f -mavx512vl -mavx512bw"
)

outdir=build/isa
mkdir -p "$outdir"

for variant in "${!ISA_FLAGS[@]}"; do
  echo "== Building $variant =="
  flags="${ISA_FLAGS[$variant]}"
  builddir="$outdir/$variant"
  cmake -S . -B "$builddir" -G Ninja \
    -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
    -DCPUFLAGS="$flags" -DARCH="$ARCH"
  ninja -C "$builddir" >/dev/null
  mkdir -p "$builddir/artifacts"
  cp "$builddir"/kernel* "$builddir/artifacts" 2>/dev/null || true
  cp "$builddir"/xv6*.img "$builddir/artifacts" 2>/dev/null || true
  echo "Built $variant with flags: $flags" > "$builddir/build.info"
done

cat <<EOM
All builds completed. Results stored in $outdir/.
Each subdirectory contains the compiled kernel and disk images.
EOM
