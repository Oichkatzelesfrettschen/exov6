#STREAMS Prototype TODOs

This file collects outstanding tasks for the prototype STREAMS implementation. The list is non-exhaustive and mainly serves as a placeholder for future development notes.

## Core functionality

- Integrate the STREAMS callbacks with the kernel scheduler to replace the current stubs.
- ~~Flesh out `streams_stop()` and `streams_yield()` so that modules can halt or
  yield control as intended. `streams_stop()` should tear down the current
  pipeline and wake the scheduler so that resources can be reclaimed.  Modules
  calling this helper must ensure any outbound messages are flushed before the
  thread exits. `streams_yield()` should temporarily hand execution back to the
  scheduler while preserving the module's state, allowing other STREAMS threads
  to make progress. The function needs to save the context of the yielding
  module and mark it runnable so that the scheduler can resume it later.~~

## Testing and tooling

- Add unit tests for the logging helpers in `examples/python/streams_log.py`.

## Flow control and configuration

- Document the PID based flow control interface under `/proc/streams/fc/`.
- Provide an example illustrating dynamic tuning via `examples/python/flow_pid.py`.

Additional issues may be recorded here as the prototype evolves.
