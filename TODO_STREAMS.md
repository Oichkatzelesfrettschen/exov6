# STREAMS TODO Ledger

This document tracks pending work related to the STREAMS prototype and
associated subsystems.  It summarises key areas that still need
implementation or refinement.

## Adaptive PID flow-control constants

`flow_pid.c` and `flow_pid.h` implement an adaptive control loop for
STREAMS flow control.  Tuning constants should be exposed via
`/proc/streams/fc/*` for runtime configuration.

## libnstr_graph.so API skeleton

A shared library, `libnstr_graph.so`, will provide basic graph
operations used by the networking STREAMS modules.  The initial API
should offer `open`, `close`, `add_edge`, `remove_edge` and `query`
functions.

## strlog_json() integration

Structured log entries should be emitted using a new `strlog_json()`
helper that serialises messages as JSON objects.  Existing logging paths
need to be updated to call this routine.

## Zone allocator hardening

The zone allocator requires additional integrity checks.  Each zone
should maintain a `zone_id` field and slabs must be tagged accordingly
so that corruption can be detected more easily.

## SVR4 linkblk parity

`compat_sv4.c` aims to match historical SVR4 interfaces.  The `linkblk`
structure and related handling need review to ensure parity with the
original implementation.
