# Multi-Architecture Builds

Phoenix supports several CPU architectures through a combination of cross
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

## SIMD and CPU Feature Flags

The optional `USE_SIMD` flag builds architecture specific math routines.
`CPUFLAGS` passes extra compiler options such as `-mavx2` or `-mfpu=neon` to
fine tune the selected instruction set.  If the compiler rejects a flag or the
option is left empty the generic C implementations remain in place so the
resulting binaries run on any compatible processor.

### Fallback Order

At run time the SIMD dispatch library probes the host CPU and chooses the
best available implementation.  On x86 the preference order is AVX, SSE2, MMX
and finally x87.  ARM builds attempt NEON while PowerPC tries AltiVec/VSX.
When none of these extensions are present the scalar routines are used.

The script `scripts/build_isa_variants.sh` demonstrates building kernels for
many of these feature sets.  Each variant ends up under `build/isa/` for
comparison and benchmarking.
