# FeuerBird Exokernel - Container Quick Start Guide

## 🚀 Get Started in 5 Minutes

This guide will get you building FeuerBird Exokernel in under 5 minutes using the optimized Docker container.

## Prerequisites

- **Docker**: [Install Docker](https://docs.docker.com/get-docker/) (Docker Desktop on Mac/Windows, Docker Engine on Linux)
- **Git**: For cloning the repository
- **5 GB free disk space**: For container and build artifacts

## Quick Start Commands

### 1. Clone and Enter Repository

```bash
git clone https://github.com/Oichkatzelesfrettschen/feuerbird_exokernel.git
cd feuerbird_exokernel
```

### 2. Build the Container (One Time)

```bash
./scripts/docker-build.sh build
```

**⏱️ Time**: 8-10 minutes first time, ~30 seconds with cache

### 3. Build the Kernel

```bash
./scripts/docker-build.sh cmake Release
```

**⏱️ Time**: 3-5 minutes

### 4. Verify Success

```bash
ls -lh build/kernel
file build/kernel
```

**Expected Output**:
```
-rwxr-xr-x 1 user user 2.3M Dec 29 12:34 build/kernel
build/kernel: ELF 64-bit LSB executable, x86-64, version 1 (SYSV)
```

## Development Workflow

### Interactive Development Shell

Start a persistent development environment:

```bash
./scripts/docker-build.sh shell
```

Inside the container, you can use all standard tools:

```bash
# CMake build
cmake -B build -G Ninja -DCMAKE_BUILD_TYPE=Debug
ninja -C build

# Meson build
meson setup builddir
ninja -C builddir

# Run tests
pytest tests/

# Format code
clang-format -i src/**/*.c

# Exit container
exit
```

### Using Docker Compose

For more complex workflows:

```bash
# Build with CMake
docker compose run cmake-build

# Build with Meson
docker compose run meson-build

# Interactive development
docker compose run dev

# Run QEMU tests
docker compose run qemu-test
```

## Common Tasks

### Clean Build

```bash
./scripts/docker-build.sh clean
./scripts/docker-build.sh cmake Release
```

### Debug Build

```bash
./scripts/docker-build.sh cmake Debug
```

### Run Tests

```bash
./scripts/docker-build.sh test
```

### Show Container Info

```bash
./scripts/docker-build.sh info
```

### Performance Benchmark

```bash
./scripts/docker-build.sh benchmark
```

## Troubleshooting

### "Docker not found"

**Solution**: Install Docker from https://docs.docker.com/get-docker/

### "Permission denied" (Linux)

**Solution**: Add your user to docker group:
```bash
sudo usermod -aG docker $USER
newgrp docker
```

### "Out of disk space"

**Solution**: Clean up Docker artifacts:
```bash
docker system prune -a
docker volume prune
```

### Slow build on Windows/Mac

**Solution**: 
- Increase Docker Desktop memory limit (8GB recommended)
- Use WSL2 on Windows for better performance
- Ensure Docker Desktop is using virtualization framework on Mac

### Build fails with "not found"

**Solution**: Rebuild the container:
```bash
./scripts/docker-build.sh build
```

## Advanced Usage

### Custom Build Flags

```bash
# CMake with LTO and Polly
docker run --rm -v $(pwd):/workspace feuerbird-builder bash -c "
  cmake -B build -G Ninja \
    -DCMAKE_BUILD_TYPE=Release \
    -DUSE_LLD=ON \
    -DUSE_LTO=ON \
    -DUSE_POLLY=ON
  ninja -C build
"
```

### Mount Custom Cache

```bash
docker run --rm \
  -v $(pwd):/workspace \
  -v feuerbird-cache:/build \
  feuerbird-builder
```

### Use Different LLVM Version

```bash
docker build --build-arg LLVM_VERSION=17 -t feuerbird-builder:llvm17 .
```

### Enable QEMU KVM Acceleration

```bash
docker run --rm \
  --device /dev/kvm:/dev/kvm \
  -v $(pwd):/workspace \
  feuerbird-builder \
  ninja -C build qemu-nox
```

## Environment Variables

Control build behavior with environment variables:

```bash
# Number of parallel build jobs
export BUILD_CPUS=4

# Memory limit
export BUILD_MEMORY=4G

# CMake build type
export CMAKE_BUILD_TYPE=Release

# Meson build type
export MESON_BUILDTYPE=release

# Then run builds
./scripts/docker-build.sh cmake
```

## Tips for Best Performance

### 1. Use BuildKit

```bash
export DOCKER_BUILDKIT=1
./scripts/docker-build.sh build
```

### 2. Named Volumes for Caching

```bash
docker volume create feuerbird-build-cache
docker compose up dev
```

### 3. Parallel Builds

The container automatically uses all CPU cores. No configuration needed!

### 4. SSD Storage

Store Docker images on SSD for 2-3x faster builds.

## What's Next?

After successfully building:

1. **Explore the Code**: Check out `kernel/`, `libos/`, and `src/`
2. **Read Documentation**: See `docs/` for architecture and design
3. **Run Tests**: `./scripts/docker-build.sh test`
4. **Modify and Build**: Make changes and rebuild quickly
5. **Contribute**: Submit pull requests with your improvements!

## Getting Help

- **Documentation**: See `docs/CONTAINER_BUILD.md` for complete reference
- **Script Help**: Run `./scripts/docker-build.sh help`
- **Issues**: Open an issue on GitHub
- **Community**: Join discussions on GitHub Discussions

## Summary of Commands

```bash
# Setup (once)
./scripts/docker-build.sh build

# Daily development
./scripts/docker-build.sh shell           # Interactive development
./scripts/docker-build.sh cmake Release   # Quick rebuild

# Testing
./scripts/docker-build.sh test            # Run tests

# Maintenance
./scripts/docker-build.sh info            # Show info
./scripts/docker-build.sh clean           # Clean builds
./scripts/docker-build.sh benchmark       # Performance test
```

---

**Ready to build?** Run `./scripts/docker-build.sh build` and get started! 🚀

**Questions?** Check out the full documentation in `docs/CONTAINER_BUILD.md`
