# Architecture Detection and Fallback

FeuerBird builds can target multiple CPU architectures. The build system passes
`ARCH` to the compiler and optionally additional instruction set extensions via
`CPUFLAGS`. When `USE_SIMD` is enabled the math routines choose specialized
implementations at compile time.

If the compiler does not advertise the requested extension, or `CPUFLAGS` is
left empty, the generic C versions remain in place so the resulting binaries run
on any compatible processor.

The helper script `scripts/build_isa_variants.sh` demonstrates how to compile a
series of x86 kernels using different CPU feature flags. It sets `CPUFLAGS` for
variants such as `-mx87`, `-mmmx`, `-msse2`, `-mavx2`, `-mfma` and `-mavx512f`.
Each build ends up in `build/isa/<variant>/`.

## Cross‑Compilation Examples

### ARM

```sh
cmake -S . -B build-aarch64 -G Ninja -DARCH=aarch64
ninja -C build-aarch64
./qemu-aarch64.sh
```

### POWER

```sh
cmake -S . -B build-ppc64 -G Ninja -DARCH=ppc64
ninja -C build-ppc64
qemu-system-ppc64 -M pseries -nographic -kernel kernel-ppc64
```

These commands produce kernels for AArch64 and 64‑bit PowerPC
respectively. Run them under QEMU or boot on real hardware as needed.
