# POSIX Test Battery

This directory contains tests for the LibOS POSIX personality.

## Running Tests

To run the test suite:

```bash
./run.py
```

This script compiles the tests against `libos` and runs them. Currently, it verifies the "Host Wrapper" configuration, which ensures that the LibOS API surface is correct and functions correctly when delegating to the host kernel (Linux).

## Test Files

*   `smoke_test.c`: Verifies basic POSIX functionality:
    *   `libos_fork` / `libos_waitpid` / `libos_exit`
    *   `libos_pipe` / `libos_read` / `libos_write`
    *   Process PID retrieval
*   `run.py`: Test runner that handles compilation flags and execution.

## Coverage

The current tests cover the basic Process and IPC APIs. Future tests should include file I/O (once the VFS is fully implemented) and signal handling.
