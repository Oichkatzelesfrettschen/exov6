# Profiling Metrics

The `feuerbird_prof` utility provides basic profiling support for FeuerBird
development builds.  It exposes counters for SIMD instruction usage and
scalar fallbacks along with timing hooks for IPC latency and context
switch duration.

For automated testing the same source is compiled as a standalone
binary named `tools/feuerbird_metrics`. The CI pipeline invokes this
helper to gather SIMD counts, scalar fallbacks and latency numbers from
the microbenchmark suite. The collected metrics are used to monitor
performance trends across ISA variants.

## Building

The tool is built as part of the standard build process:

```bash
$ meson setup build
$ ninja -C build feuerbird_prof
```

or with CMake:

```bash
$ cmake -S . -B build -G Ninja
$ cmake --build build --target feuerbird_prof
```

## Example Usage

```c
#include "feuerbird_metrics.h"

feuerbird_metrics_reset();
feuerbird_metrics_record_ipc_start();
// perform IPC operation
feuerbird_metrics_record_ipc_end();

printf("simd=%llu scalar=%llu\n",
       (unsigned long long)feuerbird_metrics_get_simd_count(),
       (unsigned long long)feuerbird_metrics_get_scalar_count());
```

The helper `benchmark_all_architectures()` runs the microbench suite for
all builds found under `build/isa/` and prints the elapsed time for each
variant.

```c
benchmark_all_architectures();
```
