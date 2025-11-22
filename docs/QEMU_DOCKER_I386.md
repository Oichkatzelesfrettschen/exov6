# i386 QEMU-in-Docker Integration Guide

This guide explains how to build and test ExoV6 as a 32-bit i386 Mach-like kernel using QEMU emulation inside Docker containers, following best practices for multi-architecture CI/CD.

## Table of Contents
1. [Overview](#overview)
2. [Architecture](#architecture)
3. [GitHub Actions Workflow](#github-actions-workflow)
4. [Local Development](#local-development)
5. [Docker Setup](#docker-setup)
6. [QEMU Configuration](#qemu-configuration)
7. [Troubleshooting](#troubleshooting)
8. [Performance](#performance)
9. [Best Practices](#best-practices)

---

## Overview

ExoV6 can be built and tested as a **32-bit i386 Mach microkernel** using:
- **QEMU i386** emulation for full system virtualization
- **Docker** containers for reproducible build environments
- **binfmt_misc** for transparent i386 binary execution on x86_64 hosts
- **GitHub Actions** for automated CI/CD

### Why QEMU-in-Docker?

1. **Reproducibility**: Docker ensures consistent build environments
2. **Multi-arch**: Test on i386, x86_64, and other architectures
3. **CI/CD**: Automate testing without bare-metal i386 hardware
4. **Isolation**: Each build runs in a clean container
5. **Flexibility**: Easy to modify CPU, memory, and hardware emulation

---

## Architecture

### Layered Approach

```
GitHub Actions Runner (x86_64)
  ├─> Docker (with Buildx multi-platform support)
  │     ├─> binfmt_misc (QEMU user-mode emulation)
  │     └─> i386 Container (linux/386)
  │           ├─> Build tools (gcc -m32, clang, cmake)
  │           └─> QEMU System Emulator (qemu-system-i386)
  │                 └─> ExoV6 i386 Kernel Boot
  │                       ├─> Pentium/Pentium3 CPU
  │                       ├─> 128-256MB RAM
  │                       └─> Serial console
```

### Key Components

1. **docker/setup-qemu-action@v3**
   - Installs QEMU static binaries
   - Configures binfmt_misc for transparent emulation
   - Supports linux/386, linux/amd64, linux/arm64, etc.

2. **docker/setup-buildx-action@v3**
   - Enables multi-platform Docker builds
   - Uses BuildKit for improved caching
   - Supports simultaneous builds for multiple architectures

3. **i386/debian:bookworm Base Image**
   - Official Debian i386 port
   - Full 32-bit userspace
   - Compatible with modern build tools

4. **qemu-system-i386**
   - Full system emulator (not user-mode)
   - Emulates 80386, Pentium, Pentium3, and other i386 CPUs
   - Supports serial console, networking, storage

---

## GitHub Actions Workflow

### Workflow File

Located at `.github/workflows/qemu-docker-i386.yml`

### Jobs

#### 1. `build-i386-docker`
Main build and test job:

**Steps:**
1. Checkout repository
2. Set up QEMU (installs binfmt handlers)
3. Set up Docker Buildx
4. Create i386 Dockerfile with:
   - Debian i386 base image
   - Build tools (gcc, clang, cmake, ninja)
   - QEMU system emulator
   - Expect scripts for automation
5. Build Docker image for linux/386 platform
6. Run build inside i386 container
7. Validate kernel binary (check for 32-bit ELF)
8. Run QEMU smoke test
9. Run QEMU integration test
10. Upload artifacts

**Key Features:**
- Docker layer caching for faster builds
- Privileged containers for QEMU virtualization
- Timeout protection (120s default)
- Expect-based automation
- Binary validation

#### 2. `qemu-docker-multiarch`
Multi-architecture validation:

**Tests:**
- linux/386 (i386)
- linux/amd64 (x86_64)

**Purpose:**
- Verify QEMU availability across platforms
- Test cross-platform compatibility

#### 3. `performance-test-i386`
Performance benchmarking:

**Metrics:**
- Boot time measurement
- Kernel startup latency
- QEMU emulation overhead

#### 4. `ci-summary`
Generates comprehensive summary of all tests.

### Triggers

**Automatic:**
- Push to master, main, develop, copilot/** branches
- Pull requests

**Manual:**
- Workflow dispatch with custom options:
  - `debug_enabled`: Enable SSH debugging
  - `qemu_timeout`: Custom timeout (default 120s)

---

## Local Development

### Prerequisites

Install Docker with BuildKit support:

```bash
# Ubuntu/Debian
sudo apt-get update
sudo apt-get install docker.io docker-buildx

# Enable BuildKit
export DOCKER_BUILDKIT=1

# Start Docker service
sudo systemctl start docker
sudo usermod -aG docker $USER
```

### Quick Start

```bash
# 1. Clone repository
git clone https://github.com/Oichkatzelesfrettschen/exov6.git
cd exov6

# 2. Build i386 Docker image
docker buildx build \
  --platform linux/386 \
  -f Dockerfile.i386 \
  -t exov6-i386:latest \
  .

# 3. Run build
docker run --rm \
  --platform linux/386 \
  -v $PWD:/workspace \
  exov6-i386:latest \
  /workspace/build-i386.sh

# 4. Test in QEMU
docker run --rm \
  --privileged \
  --platform linux/386 \
  exov6-i386:latest \
  qemu-system-i386 \
    -kernel /workspace/build-i386/kernel.elf \
    -m 256M \
    -cpu pentium3 \
    -nographic
```

### Manual Dockerfile Creation

```dockerfile
FROM i386/debian:bookworm

# Install dependencies
RUN dpkg --add-architecture i386 && \
    apt-get update && \
    apt-get install -y \
    build-essential:i386 \
    gcc:i386 \
    cmake \
    ninja-build \
    qemu-system-x86 \
    && rm -rf /var/lib/apt/lists/*

# Set 32-bit flags
ENV CFLAGS="-m32 -march=i386"
ENV CXXFLAGS="-m32 -march=i386"
ENV LDFLAGS="-m32"

WORKDIR /workspace
```

---

## Docker Setup

### Multi-Platform Build

```bash
# Install QEMU binfmt support
docker run --rm --privileged \
  multiarch/qemu-user-static \
  --reset -p yes

# Verify platforms
docker buildx ls

# Create builder
docker buildx create \
  --name exov6-builder \
  --driver docker-container \
  --use

# Build for multiple platforms
docker buildx build \
  --platform linux/386,linux/amd64 \
  -t exov6:latest \
  --push \
  .
```

### Using docker-compose

```yaml
version: '3.8'

services:
  build-i386:
    image: i386/debian:bookworm
    platform: linux/386
    volumes:
      - .:/workspace
    working_dir: /workspace
    command: |
      bash -c "
        apt-get update &&
        apt-get install -y build-essential cmake ninja-build &&
        mkdir -p build-i386 &&
        cd build-i386 &&
        cmake -G Ninja -DCMAKE_C_FLAGS='-m32' .. &&
        ninja
      "
  
  test-qemu:
    image: i386/debian:bookworm
    platform: linux/386
    privileged: true
    volumes:
      - .:/workspace
    command: |
      bash -c "
        apt-get update &&
        apt-get install -y qemu-system-x86 &&
        qemu-system-i386 \
          -kernel /workspace/build-i386/kernel.elf \
          -m 256M \
          -nographic
      "
```

Run with:
```bash
docker-compose up build-i386
docker-compose up test-qemu
```

---

## QEMU Configuration

### CPU Models for i386

```bash
# List available i386 CPUs
qemu-system-i386 -cpu help

# Recommended CPUs for Mach-like kernels:
# - pentium      (80586, 1993, basic)
# - pentium2     (80686, 1997, MMX)
# - pentium3     (80686, 1999, SSE)
# - qemu32       (Generic 32-bit, safe default)
```

### Basic QEMU Invocation

```bash
qemu-system-i386 \
  -kernel build-i386/kernel.elf \
  -m 256M \
  -cpu pentium3 \
  -smp 2 \
  -nographic \
  -no-reboot \
  -serial mon:stdio \
  -d guest_errors
```

### Advanced Options

**With Disk Image:**
```bash
qemu-system-i386 \
  -kernel kernel.elf \
  -hda filesystem.img \
  -m 256M \
  -cpu pentium3
```

**With Networking:**
```bash
qemu-system-i386 \
  -kernel kernel.elf \
  -m 256M \
  -netdev user,id=net0 \
  -device ne2k_pci,netdev=net0
```

**With Graphics (for local testing):**
```bash
qemu-system-i386 \
  -kernel kernel.elf \
  -m 256M \
  -vga std \
  -display gtk
```

**Debug Mode:**
```bash
qemu-system-i386 \
  -kernel kernel.elf \
  -m 256M \
  -s \
  -S \
  -nographic

# In another terminal:
gdb kernel.elf
(gdb) target remote :1234
(gdb) c
```

---

## Troubleshooting

### Common Issues

#### 1. "exec user process caused: exec format error"

**Cause**: binfmt_misc not configured

**Fix**:
```bash
docker run --rm --privileged \
  multiarch/qemu-user-static \
  --reset -p yes

# Verify
docker run --rm --platform linux/386 i386/debian:bookworm uname -m
# Should output: i686
```

#### 2. Docker build fails with "no matching manifest"

**Cause**: Platform not enabled in Buildx

**Fix**:
```bash
docker buildx create --use --name multiarch
docker buildx inspect --bootstrap
```

#### 3. QEMU fails with "Could not access KVM kernel module"

**Cause**: KVM not available (expected in Docker)

**Fix**: This is normal. QEMU falls back to TCG (software emulation). No action needed.

#### 4. "Permission denied" when running Docker

**Cause**: User not in docker group

**Fix**:
```bash
sudo usermod -aG docker $USER
newgrp docker
```

#### 5. Build is very slow

**Cause**: QEMU user-mode emulation overhead

**Solutions**:
- Use Docker layer caching
- Enable BuildKit: `export DOCKER_BUILDKIT=1`
- Increase resources in Docker settings
- Use native i386 hardware if available

#### 6. Kernel doesn't boot in QEMU

**Cause**: Kernel not compiled for i386

**Fix**:
```bash
# Verify kernel is 32-bit
file build-i386/kernel.elf
# Should show: ELF 32-bit LSB executable, Intel 80386

# If not, rebuild with:
cmake -DARCH=i386 -DCMAKE_C_FLAGS="-m32" ..
```

#### 7. "qemu-system-i386: command not found" in container

**Cause**: QEMU not installed in container

**Fix**: Add to Dockerfile:
```dockerfile
RUN apt-get update && apt-get install -y qemu-system-x86
```

---

## Performance

### Optimization Tips

**1. Docker Layer Caching**
```yaml
- uses: actions/cache@v3
  with:
    path: /tmp/.buildx-cache
    key: ${{ runner.os }}-buildx-i386-${{ hashFiles('**/Dockerfile') }}
```

**2. Use BuildKit**
```bash
export DOCKER_BUILDKIT=1
export COMPOSE_DOCKER_CLI_BUILD=1
```

**3. Parallel Builds**
```bash
ninja -j $(nproc)
# or
make -j $(nproc)
```

**4. Reduce Image Size**
```dockerfile
# Multi-stage build
FROM i386/debian:bookworm AS builder
RUN apt-get update && apt-get install -y build-essential
COPY . /src
RUN cd /src && make

FROM i386/debian:bookworm-slim
COPY --from=builder /src/kernel.elf /kernel.elf
```

### Benchmarks

Typical performance on GitHub Actions runners:

| Operation | Time |
|-----------|------|
| Docker image build | 3-5 minutes |
| Kernel compile | 2-4 minutes |
| QEMU boot test | 10-30 seconds |
| Full CI workflow | 8-12 minutes |

**Emulation overhead**: QEMU i386 on x86_64 typically runs at 30-50% of native speed.

---

## Best Practices

### 1. Use Official Actions

```yaml
- uses: docker/setup-qemu-action@v3
- uses: docker/setup-buildx-action@v3
- uses: docker/build-push-action@v6
```

### 2. Pin Versions

```dockerfile
FROM i386/debian:bookworm  # Specific version, not :latest
```

### 3. Minimize Layers

```dockerfile
# Bad: Multiple RUN commands
RUN apt-get update
RUN apt-get install -y gcc
RUN apt-get install -y cmake

# Good: Single RUN with cleanup
RUN apt-get update && \
    apt-get install -y gcc cmake && \
    rm -rf /var/lib/apt/lists/*
```

### 4. Use .dockerignore

```
build*/
.git/
*.o
*.a
*.log
```

### 5. Privileged Containers Only When Needed

```bash
# For QEMU system emulation
docker run --privileged ...

# For builds (no --privileged needed)
docker run ...
```

### 6. Timeout Protection

```yaml
jobs:
  build:
    timeout-minutes: 60
```

```bash
timeout 120s qemu-system-i386 ...
```

### 7. Automate Testing

```bash
#!/usr/bin/expect -f
set timeout 120
spawn qemu-system-i386 -kernel kernel.elf
expect "ExoV6" { send_user "✅ Boot OK\n" }
expect timeout { send_user "❌ Timeout\n"; exit 1 }
```

### 8. Artifact Management

```yaml
- uses: actions/upload-artifact@v3
  with:
    name: kernel-i386
    path: build-i386/kernel.elf
    retention-days: 14
```

---

## Resources

### Official Documentation

- [Docker Multi-Platform Builds](https://docs.docker.com/build/ci/github-actions/multi-platform/)
- [docker/setup-qemu-action](https://github.com/docker/setup-qemu-action)
- [docker/setup-buildx-action](https://github.com/docker/setup-buildx-action)
- [QEMU i386 System Emulation](https://www.qemu.org/docs/master/system/target-i386.html)

### Example Projects

- [GNU Hurd Docker](https://github.com/Oichkatzelesfrettschen/gnu-hurd-docker) - Mach microkernel in Docker
- [Linux Kernel CI](https://github.com/torvalds/linux) - Large-scale kernel testing
- [OSv](https://github.com/cloudius-systems/osv) - QEMU-based OS testing

### Tools

- [multiarch/qemu-user-static](https://github.com/multiarch/qemu-user-static) - QEMU binfmt setup
- [Expect](https://core.tcl-lang.org/expect/index) - Automation scripting
- [BuildKit](https://github.com/moby/buildkit) - Next-gen Docker builds

---

## See Also

- `doc/QEMU_INTEGRATION.md` - Native QEMU integration
- `.github/workflows/qemu-ci.yml` - x86_64 QEMU workflow
- `.github/workflows/qemu-docker-i386.yml` - This workflow
- `DOCUMENTATION.md` - Complete ExoV6 documentation
- `user/README.md` - Userland organization
