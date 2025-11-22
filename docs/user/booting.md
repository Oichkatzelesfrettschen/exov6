# Booting in QEMU

This guide explains how to boot and run the FeuerBird/ExoV6 system using QEMU.

## Quick Start

### Prerequisites

Install QEMU and build tools:

```bash
# Ubuntu/Debian
sudo apt-get install -y qemu-system-x86 qemu-system-arm build-essential cmake ninja-build

# macOS
brew install qemu cmake ninja
```

### Build and Run

```bash
# Configure
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release

# Build
ninja -C build

# Run in QEMU (No Graphics)
ninja -C build qemu-nox
```

## Running the System

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
ninja -C build qemu-nox

# With graphics
ninja -C build qemu
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

## Advanced Options

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
    -netdev user,id=net0,hostfwd=tcp::5555-:22 \
    -device e1000,netdev=net0 \
    -nographic
```

### Storage Options

```bash
# virtio (fastest)
qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -drive file=build/fs.img,if=virtio,format=raw \
    -m 256M
```

## Performance Testing

### Boot Time Measurement

```bash
/usr/bin/time -v qemu-system-x86_64 \
    -kernel build/kernel.elf \
    -m 256M \
    -nographic \
    -no-reboot
```

## Troubleshooting

If the system fails to boot, check the following:

1.  **Kernel Format**: Ensure `build/kernel.elf` is a valid x86-64 ELF binary.
2.  **BIOS/ROM**: If you see "Could not open ROM", install `seabios` or `ovmf`.
3.  **Hangs**: Use `timeout` to prevent indefinite hangs during automated runs.

For detailed debugging instructions (GDB, tracing), see [Debugging Guide](../dev/debugging.md).
