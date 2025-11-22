# Crash Handling Discipline

## Overview
Robust crash handling ensures that system failures are recoverable or, at minimum, diagnosable.

## Kernel Panic
When the kernel encounters an unrecoverable error:
1.  **Freeze**: Disable interrupts and stop other cores.
2.  **Dump State**: Print CPU registers (`RIP`, `RSP`, `RAX`...), control registers (`CR2`, `CR3`), and the stack trace.
3.  **Preserve Logs**: Flush the kernel log buffer to the serial console or persistent storage (if available).
4.  **Reboot**: Wait for user input or watchdog timeout to reboot.

## Post-Mortem Analysis

### 1. Core Dumps
*   **Kernel**: (Planned) Write physical memory to a crash partition or network server (kdump).
*   **User**: LibOS generates core dumps for crashed processes, written to the filesystem.

### 2. Analysis Tools
*   **GDB**: Load the kernel ELF and the core dump to inspect the state.
*   **Addr2line**: Translate instruction pointers to source lines.

## Recovery Strategies

### 1. Process Resurrection
The "Resurrection Server" (`kernel/resurrection/`) monitors critical system processes. If a driver or service crashes, it can be restarted with a clean state, utilizing the exokernel's isolation to prevent whole-system failure.

### 2. Micro-Reboots
For transient hardware faults, individual subsystems can be reset without a full system reboot.
