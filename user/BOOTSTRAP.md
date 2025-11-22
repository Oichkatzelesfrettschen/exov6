# Userland Bootstrap Sequence

This document describes how the Phoenix Exokernel boots into a minimal login shell.

## 1. Kernel Initialization
The kernel initializes hardware, memory management, and the first process (PID 1).

## 2. Init Process (PID 1)
The kernel loads the `init` user program. `init` is responsible for:
1. Initializing the console/standard I/O.
2. Mounting necessary filesystems (if any).
3. Spawning the shell (`sh`).

## 3. Bootstrap Script (Conceptual)
If `init` were a script, it would look like this:

```sh
#!/bin/sh
# Mount root filesystem (handled by kernel usually, but maybe...)
# mount -t ext2 /dev/sda1 /

# Set up environment
export PATH=/bin

# Start shell
exec sh
```

## 4. Verification
To verify the bootstrap sequence:
1. Build the userland: `make userland` (or `cmake --build .`)
2. Run the system (e.g., in QEMU).
3. Observe `init` starting.
4. `init` fork/execs `sh`.
5. `sh` prints a prompt (`$ `).

## 5. Bootstrap Test
The `user/init.c` source code serves as the implementation of this sequence.
