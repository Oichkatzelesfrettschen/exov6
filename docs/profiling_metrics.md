# Profiling Metrics

The `phoenix_prof` utility provides basic profiling support for Phoenix
development builds.  It exposes counters for SIMD instruction usage and
scalar fallbacks along with timing hooks for IPC latency and context
switch duration.

## Building

The tool is built as part of the standard build process:

```bash
$ meson setup build
$ ninja -C build phoenix_prof
```

or with CMake:

```bash
$ cmake -S . -B build -G Ninja
$ cmake --build build --target phoenix_prof
```

## Example Usage

```c
#include "profiling/phoenix_metrics.h"

phoenix_metrics_reset();
phoenix_metrics_record_ipc_start();
// perform IPC operation
phoenix_metrics_record_ipc_end();

printf("simd=%llu scalar=%llu\n",
       (unsigned long long)phoenix_metrics_get_simd_count(),
       (unsigned long long)phoenix_metrics_get_scalar_count());
```

The helper `benchmark_all_architectures()` runs the microbench suite for
all builds found under `build/isa/` and prints the elapsed time for each
variant.

```c
benchmark_all_architectures();
```
