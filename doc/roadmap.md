#FeuerBird Roadmap

This document summarizes the current milestones and open tasks for the FeuerBird exokernel project. It draws from the [project charter](charter.md) and the STREAMS TODO list.

## Milestones from the Charter

FeuerBird aims to:

- Build a small capability based exokernel that exposes hardware resources directly to user space.
- Provide a flexible libOS implementing POSIX, BSD and SVR4 personalities without bloating the kernel.
- Encourage experimentation with scheduling models, typed channels and user space drivers.
- Keep the code understandable so new contributors can easily get involved.

These goals are paired with a lightweight governance model that welcomes contributions from anyone willing to follow the pre-commit hooks and discuss larger features on the mailing list.

## Open STREAMS Tasks

The prototype STREAMS stack still requires several features:

- **Done:** integrate STREAMS callbacks with the kernel scheduler and implement `streams_stop()` / `streams_yield()`.
- Document the PID based flow control interface under `/proc/streams/fc/` and provide an example using `examples/python/flow_pid.py`.

## Development Goals

### Short Term

- Kernel: solidify capability primitives and complete scheduler hooks for STREAMS.
- libOS: ensure basic POSIX compatibility and expose simple driver helpers.
- Scheduler: finish DAG and Beatty integration so user schedulers can chain tasks efficiently.
- Driver model: run drivers fully in user space with Cap'n Proto RPC and restart via the `rcrs` supervisor.

### Medium Term

- Kernel: support multiple cooperating microkernels and refine interrupt queueing.
- libOS: flesh out BSD and SVR4 layers while keeping the base lean.
- Scheduler: provide tooling to visualize DAG execution and tune Beatty weights.
- Driver model: document capability requirements and publish more example drivers.

### Long Term

- Kernel: mature the capability system and research new security policies (see `doc/security_policy_research.md` for an outline of research areas).
- libOS: maintain POSIX compliance as features grow, keeping most logic outside the kernel (see `libos/compatibility_roadmap.md` for detailed roadmap).
- Scheduler: experiment with alternative models and allow hot-swapping of schedulers (e.g., via `exo_stream_hot_swap` for graceful transitions).
- Driver model: evolve toward a robust user space framework that isolates misbehaving drivers and supports dynamic restarts.
- Performance: empirically validate analytical performance bounds (see `docs/empirical_performance_validation.md`).
