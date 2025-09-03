# Analysis Report: `read_file` for `doc/multi_architecture.md`

## Tool Call:
```
default_api.read_file(absolute_path = "/Users/eirikr/Documents/GitHub/exov6/doc/multi_architecture.md")
```

## Output:
```markdown
# Multi-Architecture Builds

FeuerBird supports several CPU architectures through a combination of cross
compilers and runtime feature detection.  The `setup.sh` helper installs
cross toolchains for the targets below and the build system selects one via
`-DARCH=<arch>`.

Supported values include:

* `x86` (32‑bit)
* `x86_64`
* `aarch64`
* `arm` (ARMv7)
* `powerpc`
* `ppc64` (big‑endian PowerPC64)
* `ppc64le` (little‑endian PowerPC64)

Additional architectures can be added by extending the CMake configuration
and providing the necessary run scripts.

## Runtime Feature Detection

When `USE_SIMD` is enabled the runtime checks the host CPU before
dispatching any vectorised routine.  `arch/simd_dispatch.c` performs the
detection using the CPUID instruction on x86 and `getauxval()` on Linux
for ARM and PowerPC.  The first supported extension found selects the
implementation used by the math helpers.

### Supported SIMD Backends

The dispatch table currently recognises the following instruction sets:

* x87 scalar floating point
* MMX
* SSE2
* SSE3
* AVX and AVX2+FMA
* AVX‑512
* NEON (ARM)
* AltiVec/VSX (PowerPC)

The order of preference on x86 ranges from AVX‑512 down through AVX2,
AVX, SSE3, SSE2, MMX and finally x87.  ARM prefers NEON while PowerPC tries
AltiVec.  If none of these are available the plain C implementations are
used instead.

## POSIX Wrappers and SIMD

User programs link against `libos.a` which exposes POSIX-style wrappers.
Those wrappers in turn call helper functions from
`user/math_core.c`.  At run time these helpers forward to the
dispatch library so applications automatically benefit from the best
available SIMD backend.  When compiled without `USE_SIMD` or when the
required extension is missing the same wrappers transparently fall back
to the scalar code paths.

## SIMD and CPU Feature Flags

The optional `USE_SIMD` flag builds architecture specific math routines.
`CPUFLAGS` passes extra compiler options such as `-mavx2` or `-mfpu=neon` to
fine tune the selected instruction set.  If the compiler rejects a flag or the
option is left empty the generic C implementations remain in place so the
resulting binaries run on any compatible processor.

### Fallback Order

At run time the SIMD dispatch library probes the host CPU and chooses the
best available implementation.  On x86 the dispatcher prefers AVX‑512,
then AVX2 with FMA, AVX, SSE3, SSE2, MMX and finally x87.  ARM builds
attempt NEON while PowerPC tries AltiVec/VSX.  When none of these
extensions are present the scalar routines are used.

The script `scripts/build_isa_variants.sh` demonstrates building kernels for
many of these feature sets.  Each variant ends up under `build/isa/` for
comparison and benchmarking.
```