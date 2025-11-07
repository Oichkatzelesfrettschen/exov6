# QEMU Integration Guide for ExoV6

This guide explains how to build, test, and debug ExoV6 using QEMU emulation instead of Docker.

## Table of Contents
1. [Quick Start](#quick-start)
2. [GitHub Actions CI](#github-actions-ci)
3. [Local Development](#local-development)
4. [Advanced QEMU Options](#advanced-qemu-options)
5. [Debugging](#debugging)
6. [Performance Testing](#performance-testing)
7. [Troubleshooting](#troubleshooting)

---

## Quick Start

### Prerequisites

Install QEMU and build tools:

```bash
# Ubuntu/Debian
sudo apt-get install -y \
    qemu-system-x86 \
    qemu-system-arm \
    build-essential \
    clang-18 \
    ninja-build \
    cmake

# Fedora
sudo dnf install -y \
    qemu-system-x86 \
    qemu-system-aarch64 \
    clang \
    ninja-build \
    cmake

# macOS
brew install qemu llvm ninja cmake
```

### Build and Run

```bash
# Configure
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release

# Build
ninja -C build

# Run in QEMU
ninja -C build qemu-nox
```

---

## GitHub Actions CI

### Workflow Overview

The `.github/workflows/qemu-ci.yml` workflow provides:

1. **Multi-architecture builds** (x86_64, i386)
2. **Automated QEMU testing** with expect scripts
3. **Integration tests** for boot, shell, filesystem
4. **Performance benchmarks**
5. **Artifact uploads** (kernels, logs)

### Workflow Jobs

#### 1. `qemu-build-test`
Builds and tests ExoV6 in QEMU across multiple configurations:
- x86_64 Release
- x86_64 Debug
- i386 Legacy

**Features:**
- Full kernel build with userland
- QEMU smoke test (no graphics)
- Integration test with expect automation
- Filesystem testing
- Log artifact upload

#### 2. `qemu-network-test`
Tests network functionality:
- TAP interface setup
- QEMU networking with e1000 emulation
- Multi-VM scenarios (planned)

#### 3. `qemu-performance-test`
Performance benchmarking:
- Optimized build (LTO, Polly)
- Boot time measurement
- Syscall latency benchmarks (planned)

### Triggering Workflows

**Automatic:**
- Push to `master`, `main`, `develop`, `copilot/**` branches
- Pull requests to `master`, `main`, `develop`

**Manual:**
```bash
# Via GitHub UI: Actions → QEMU Build & Test → Run workflow
# Or via gh CLI:
gh workflow run qemu-ci.yml
```

### Viewing Results

1. Go to repository **Actions** tab
2. Click on workflow run
3. Download artifacts:
   - `kernel-x86_64-Release` - Kernel binary
   - `qemu-logs-*` - QEMU output logs

---

## Local Development

### Basic QEMU Invocation

```bash
# No graphics (serial console only)
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -smp 2 \
    -nographic \
    -no-reboot \
    -serial mon:stdio

# With graphics
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 512M \
    -smp 4 \
    -vga std \
    -serial stdio
```

### Using CMake Targets

```bash
# No graphics
make qemu-nox
# or
ninja -C build qemu-nox

# With graphics
make qemu
# or
ninja -C build qemu

# With GDB debugging
make qemu-gdb
# or
ninja -C build qemu-gdb
```

### With Filesystem Image

```bash
# Build filesystem
ninja -C build fs.img

# Run with filesystem
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -drive file=build/fs.img,format=raw,index=0,media=disk \
    -m 512M \
    -nographic
```

---

## Advanced QEMU Options

### Multi-core Testing

```bash
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 1G \
    -smp cores=4,threads=2,sockets=1 \
    -nographic
```

### Network Configuration

```bash
# User-mode networking (NAT)
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -netdev user,id=net0,hostfwd=tcp::5555-:22 \
    -device e1000,netdev=net0 \
    -nographic

# TAP networking (requires setup)
sudo ip tuntap add dev tap0 mode tap user $USER
sudo ip link set tap0 up
sudo ip addr add 10.0.2.1/24 dev tap0

qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -netdev tap,id=net0,ifname=tap0,script=no,downscript=no \
    -device e1000,netdev=net0 \
    -nographic
```

### Storage Options

```bash
# IDE disk
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -hda build/fs.img \
    -m 256M

# AHCI (SATA)
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -drive file=build/fs.img,if=none,id=disk0 \
    -device ahci,id=ahci \
    -device ide-hd,drive=disk0,bus=ahci.0 \
    -m 256M

# virtio (fastest)
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -drive file=build/fs.img,if=virtio,format=raw \
    -m 256M
```

### Trace and Debug Options

```bash
# Guest error logging
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -d guest_errors,int,cpu_reset \
    -D qemu-debug.log

# CPU trace
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -d in_asm,out_asm,exec \
    -D cpu-trace.log

# Monitor mode (interactive)
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -monitor stdio
```

---

## Debugging

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

---

## Performance Testing

### Boot Time Measurement

```bash
/usr/bin/time -v qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -nographic \
    -no-reboot

# Extract boot time from log
grep "Elapsed" 
```

### Automated Testing with Expect

Create `test.exp`:
```expect
#!/usr/bin/expect -f
set timeout 30

spawn qemu-system-x86_64 -kernel build/kernel.elf -m 256M -nographic

expect {
    "ExoV6" { send_user "✅ Boot successful\n" }
    timeout { send_user "❌ Boot failed\n"; exit 1 }
}

expect {
    -re "\\$|#|>" { send "ls\r" }
    timeout { exit 1 }
}

expect {
    -re "\\$|#|>" { send_user "✅ Shell works\n" }
    timeout { exit 1 }
}

send "\x01x"  # Ctrl-A x to quit
expect eof
```

Run:
```bash
chmod +x test.exp
./test.exp
```

### Benchmarking Syscalls

```bash
# Inside QEMU, run usertests
(kernel) $ ./usertests

# Or automate
echo "./usertests" | qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -nographic \
    -no-reboot
```

---

## Troubleshooting

### Common Issues

**1. Kernel doesn't boot**
```bash
# Check kernel format
file build/kernel.elf

# Should show: ELF 64-bit LSB executable, x86-64

# Try with more verbose output
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -d guest_errors,cpu_reset,int \
    -D debug.log \
    -nographic
```

**2. "Could not open ROM" errors**
```bash
# Install BIOS files
sudo apt-get install seabios ovmf

# Or specify explicitly
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -bios /usr/share/seabios/bios.bin \
    -nographic
```

**3. No output in serial console**
```bash
# Ensure kernel outputs to serial port
# Check kernel early boot code

# Try different serial options
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -serial mon:stdio \
    -nographic
```

**4. QEMU hangs**
```bash
# Use timeout wrapper
timeout 60s qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -nographic

# Or add -no-reboot to exit on panic
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -no-reboot \
    -nographic
```

**5. Triple fault/reboot loop**
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

### Exiting QEMU

- **Graphics mode**: Close window or `Ctrl+Alt+Q`
- **No graphics**: `Ctrl+A` then `X`
- **GDB mode**: `quit` in GDB, then kill QEMU
- **Force kill**: `pkill qemu` or `killall qemu-system-x86_64`

---

## Best Practices

### CI/CD Integration

1. **Use timeouts**: Always wrap QEMU in `timeout` to prevent hanging jobs
2. **Capture logs**: Redirect QEMU output for debugging
3. **Artifact uploads**: Save kernels and logs for inspection
4. **Matrix testing**: Test multiple architectures and configurations
5. **Automated validation**: Use expect scripts for consistent testing

### Development Workflow

1. **Rapid iteration**: Use `ninja qemu-nox` for quick testing
2. **Debug builds**: Use `-DCMAKE_BUILD_TYPE=Debug` for GDB symbols
3. **Serial console**: Always test with `-nographic` first
4. **Incremental testing**: Test one feature at a time
5. **Bisect failures**: Use git bisect with automated QEMU tests

### Performance Optimization

1. **KVM acceleration**: Use `-enable-kvm` on Linux hosts
2. **CPU matching**: `-cpu host` for optimal performance
3. **Memory**: Allocate appropriate RAM (-m)
4. **Disk I/O**: Use virtio for best performance
5. **SMP**: Test with multiple cores early

---

## Resources

- **QEMU Documentation**: https://www.qemu.org/docs/master/
- **QEMU Networking**: https://wiki.qemu.org/Documentation/Networking
- **GDB Manual**: https://sourceware.org/gdb/current/onlinedocs/gdb/
- **Expect Tutorial**: https://www.tcl.tk/man/expect5.31/expect.1.html

## See Also

- `DOCUMENTATION.md` - Complete ExoV6 documentation
- `user/README.md` - Userland organization
- `kernel/resurrection/README.md` - Process resurrection server
- `.github/workflows/qemu-ci.yml` - CI workflow configuration
