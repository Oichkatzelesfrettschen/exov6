# Debugging Guide

This guide explains how to debug the FeuerBird/ExoV6 kernel and LibOS using QEMU and GDB.

## QEMU Debugging

### GDB Remote Debugging

**Terminal 1: Start QEMU with GDB server**
```bash
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -s \
    -S \
    -nographic
```
- `-s`: GDB server on localhost:1234
- `-S`: Pause at startup

**Terminal 2: Connect GDB**
```bash
gdb build/kernel.elf

(gdb) target remote localhost:1234
(gdb) b main
(gdb) c
(gdb) layout src
(gdb) info registers
```

### Using CMake GDB Target

```bash
# Start QEMU paused
make qemu-gdb
# or
ninja -C build qemu-gdb

# In another terminal
gdb build/kernel.elf
(gdb) target remote :1234
(gdb) c
```

### Advanced GDB Commands

```gdb
# Hardware breakpoints
(gdb) hbreak *0x100000

# Watch memory
(gdb) watch *(int*)0x200000

# Examine page tables
(gdb) x/16xw $cr3

# Disassemble
(gdb) disas /r main

# Backtrace all threads
(gdb) thread apply all bt
```

## Trace and Debug Options

### Guest Error Logging
```bash
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -d guest_errors,int,cpu_reset \
    -D qemu-debug.log
```

### CPU Trace
```bash
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -d in_asm,out_asm,exec \
    -D cpu-trace.log
```

### Monitor Mode (Interactive)
```bash
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -monitor stdio
```

## Troubleshooting Common Issues

**1. Kernel doesn't boot**
```bash
# Check kernel format
file build/kernel.elf
# Should show: ELF 64-bit LSB executable, x86-64
```

**2. Triple fault/reboot loop**
```bash
# Enable debug output
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -d int,cpu_reset,guest_errors \
    -D qemu.log \
    -nographic

# Check qemu.log for fault details
grep -A5 "Triple fault" qemu.log
```

## Visualizing Header Dependencies

The script `tools/header_graph.py` scans the codebase for `#include` directives and emits a [DOT](https://graphviz.org/) representation.

```sh
python tools/header_graph.py -o doc/header_graph.dot
```
