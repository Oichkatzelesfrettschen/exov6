# STREAMS Prototype TODOs

This file collects outstanding tasks for the prototype STREAMS implementation. The list is non-exhaustive and mainly serves as a placeholder for future development notes.

## Core functionality

- Integrate the STREAMS callbacks with the kernel scheduler to replace the current stubs.
- Flesh out `streams_stop()` and `streams_yield()` so that modules can halt or yield control as intended.

## Testing and tooling

- Expand the latency harness in `scripts/simulate.py` to cover more module combinations.
- Add unit tests for the logging helpers in `streams_log.py`.

## Flow control and configuration

- Document the PID based flow control interface under `/proc/streams/fc/`.
- Provide an example illustrating dynamic tuning via `flow_pid.py`.

Additional issues may be recorded here as the prototype evolves.
