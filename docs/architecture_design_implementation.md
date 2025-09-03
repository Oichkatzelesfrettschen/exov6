# FeuerBird Architecture, Design, and Implementation

This document synthesizes the current architecture of the FeuerBird exokernel
project as reflected in the source tree and accompanying documentation.
It is intended as a modern roadmap for future refactoring under ISO C17 with strict POSIX-2024 (SUSv5) conformance.

## 1. Architectural Overview

FeuerBird follows the exokernel philosophy: the kernel multiplexes hardware
resources while a flexible libOS exposes POSIX, BSD, and SVR4 personalities.
Capabilities are the fundamental access tokens. They mediate low‑level
operations such as memory mapping, interrupt handling, and IPC.

### 1.1 Kernel Subsystems

- **Capability System** – manages capability tables and badge tracking. The
  design is outlined in `doc/formal_delegation_algebra_specification.md` and
  implemented in `kernel/cap*.c`.
- **Typed IPC Channels** – built on lattice‑based security primitives from
  `docs/formal_domain_lattice_specification.md` and `docs/formal_vector_timestamp_protocol_specification.md`.
- **Scheduler** – Beatty DAG scheduler (`kernel/beatty_sched.c`) supports user
  defined scheduling graphs. STREAMS integration is documented in
  `doc/streams_flow_control.md`.
- **Hypervisor Stub** – experimental interface described in `doc/hypervisor.md`
  that exposes virtualization features via capabilities.

### 1.2 User Space

User programs link against `libos` which provides the POSIX compatibility layer
tracked in `doc/posix_roadmap.md`. Example drivers live in `engine/` and
`examples/`.

## 2. Codebase Metrics

Recent automated analysis gives a sense of scale:

- `cloc` reports **526k** lines of code across **2631** files with
**115k** blank lines and **11k** comment lines.
- `lizard` scanned **1411** functions totalling **27k** non‑blank lines with an
average cyclomatic complexity of **2.8**.
- `cscope` generates `cscope.out` indexing every symbol for quick lookup.
- `graphviz` is available for constructing call graphs and scheduler diagrams.
- `networkx` enables programmatic traversal of lattice graphs to validate IPC
  dependencies and service relationships.

These metrics are generated periodically via repository tooling and aid
prioritizing refactoring work.

## 3. Design Goals

1. **Modern C17 Compliance** – all compilation units should build with
   `-std=c17`. The build system currently uses mixed standards; migration is
   ongoing.
2. **Functional Decomposition** – deeply nested logic should be refactored into
   concise static functions with Doxygen comments as mandated by `AGENTS.md`.
3. **Capability‑First Security** – the domain lattice and delegation algebra
   provide the formal basis for process isolation. Future work must ensure
   capability revocation and audit trails are efficient.
4. **Modular libOS** – POSIX layers must remain separate from the kernel. The
   roadmap documents phased implementation toward full compatibility.
5. **Documentation Synchronization** – every change requires running
   `doxygen docs/Doxyfile` and `make -C docs/sphinx`.

## 4. Future Work

- **C17 Refactoring** – adopt portable `_Static_assert`, feature-test macros, and standard idioms.
  initializer syntax across the code base.
- **Scheduler Visualization** – integrate graph generation tooling from
  `tools/scheduler_visualizer.py` with the Beatty DAG infrastructure to aid debugging.
- **Hypervisor Expansion** – extend capability support for guest I/O and memory
  mapping; document in an updated hypervisor specification.
- **POSIX Test Coverage** – increase pytest coverage as outlined in
  `doc/posix_roadmap.md` to validate the libOS.
- **Performance Modeling** – apply results from
  `docs/analytical_performance_bounds.md` to guide optimization efforts.

## 5. Conclusion

FeuerBird is evolving toward a compact exokernel with a capability‑oriented
security model. Continued modernization, improved documentation, and rigorous
analysis will ensure the project remains a useful research platform.
