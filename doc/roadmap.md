#Phoenix Roadmap

This document summarizes the current milestones and open tasks for the Phoenix exokernel project. It draws from the [project charter](charter.md) and the STREAMS TODO list.

## Milestones from the Charter

Phoenix aims to:

- Build a small capability based exokernel that exposes hardware resources directly to user space.
- Provide a flexible libOS implementing POSIX, BSD and SVR4 personalities without bloating the kernel.
- Encourage experimentation with scheduling models, typed channels and user space drivers.
- Keep the code understandable so new contributors can easily get involved.

These goals are paired with a lightweight governance model that welcomes contributions from anyone willing to follow the pre-commit hooks and discuss larger features on the mailing list.

## Open STREAMS Tasks

The prototype STREAMS stack still requires several features:

- **Done:** integrate STREAMS callbacks with the kernel scheduler and implement `streams_stop()` / `streams_yield()`.
- Expand the latency harness in `scripts/streams_latency.py` and add unit tests for `scripts/streams_log.py`.
- Document the PID based flow control interface under `/proc/streams/fc/` and provide an example using `scripts/flow_pid.py`.

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

- Kernel: mature the capability system and research new security policies.
- libOS: maintain POSIX compliance as features grow, keeping most logic outside the kernel.
- Scheduler: experiment with alternative models and allow hot-swapping of schedulers.
- Driver model: evolve toward a robust user space framework that isolates misbehaving drivers and supports dynamic restarts.
