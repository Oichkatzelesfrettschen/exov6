#!/usr/bin/env bash
set -euo pipefail

# Build xv6 for multiple x86 CPU feature sets.
# The Makefile accepts CPUFLAGS to extend compiler and assembler flags.

ARCH=${ARCH:-x86_64}
MAKECMD=${MAKECMD:-make}

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
  # Clean before each build to avoid mixing objects
  $MAKECMD clean >/dev/null || true
  CPUFLAGS="$flags" ARCH="$ARCH" $MAKECMD -j"$(nproc)" >/dev/null
  mkdir -p "$outdir/$variant"
  cp kernel* "$outdir/$variant/" 2>/dev/null || true
  cp xv6*.img "$outdir/$variant/" 2>/dev/null || true
  echo "Built $variant with flags: $flags" > "$outdir/$variant/build.info"
done

cat <<EOM
All builds completed. Results stored in $outdir/.
Each subdirectory contains the compiled kernel and disk images.
EOM
