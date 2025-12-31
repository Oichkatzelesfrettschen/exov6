# FeuerBird Exokernel - Container Build Environment

## Overview

This document describes the optimized Docker container build environment for FeuerBird Exokernel. The container provides a **fast, stable, and compatible** build environment with all necessary tools pre-configured.

## Why Use Containers?

✅ **Consistency**: Same build environment across all developers and CI systems  
✅ **Isolation**: No conflicts with host system dependencies  
✅ **Portability**: Build on any platform that supports Docker  
✅ **Reproducibility**: Versioned and documented build environment  
✅ **Speed**: Optimized with BuildKit caching and parallel builds  

## Container Features

### Optimization Highlights

1. **Multi-stage Build**: Separates build environment from runtime, minimal final image
2. **Ubuntu 24.04 LTS**: Maximum compatibility with glibc and kernel tools
3. **LLVM 18 Toolchain**: Latest Clang, LLD, and Polly optimizations
4. **BuildKit Caching**: Fast rebuilds with intelligent layer caching
5. **Parallel Builds**: Automatic detection and use of all available CPUs
6. **Non-root User**: Security best practice, UID 1000 for compatibility

### Installed Tools

- **Compilers**: Clang 18, Clang++ 18 (with C17/C++17 support)
- **Linker**: LLD 18 (LLVM linker for faster linking)
- **Build Systems**: CMake 3.28+, Meson 1.3+, Ninja
- **LLVM Tools**: llvm-ar, llvm-nm, llvm-objdump, opt, clang-tidy, clang-format
- **Kernel Tools**: bc, bison, flex, libelf-dev, libssl-dev
- **Emulation**: QEMU (x86, ARM, AArch64)
- **Python**: Python 3.12+ with pytest, black, mypy, sphinx
- **Version Control**: Git

## Quick Start

### 1. Build the Container Image

```bash
# Using the helper script (recommended)
./scripts/docker-build.sh build

# Or using docker-compose
docker-compose build builder

# Or using Docker directly
docker build -t feuerbird-builder .
```

### 2. Build the Kernel

```bash
# CMake build
./scripts/docker-build.sh cmake Release

# Meson build
./scripts/docker-build.sh meson debugoptimized

# Using docker-compose
docker-compose run cmake-build
docker-compose run meson-build
```

### 3. Interactive Development

```bash
# Start interactive shell
./scripts/docker-build.sh shell

# Or with docker-compose
docker-compose run dev

# Inside container, build as usual:
cmake -B build -G Ninja && ninja -C build
```

## Usage Guide

### Helper Script Commands

The `scripts/docker-build.sh` script provides convenient commands:

```bash
# Build container image
./scripts/docker-build.sh build

# CMake builds
./scripts/docker-build.sh cmake Debug
./scripts/docker-build.sh cmake Release
./scripts/docker-build.sh cmake RelWithDebInfo

# Meson builds
./scripts/docker-build.sh meson debug
./scripts/docker-build.sh meson release
./scripts/docker-build.sh meson debugoptimized

# Interactive shell
./scripts/docker-build.sh shell

# Run tests
./scripts/docker-build.sh test

# Clean build artifacts
./scripts/docker-build.sh clean

# Show container info
./scripts/docker-build.sh info

# Performance benchmark
./scripts/docker-build.sh benchmark
```

### Docker Compose Services

```bash
# Build with CMake
docker-compose run cmake-build

# Build with Meson
docker-compose run meson-build

# Run QEMU tests
docker-compose run qemu-test

# Interactive development shell
docker-compose run dev

# Start persistent dev environment
docker-compose up -d dev
docker-compose exec dev bash
```

### Direct Docker Commands

```bash
# Build image
docker build -t feuerbird-builder .

# Run build
docker run --rm -v $(pwd):/workspace feuerbird-builder bash -c "
  cmake -B build -G Ninja && ninja -C build
"

# Interactive shell
docker run --rm -it -v $(pwd):/workspace feuerbird-builder

# Run tests
docker run --rm -v $(pwd):/workspace feuerbird-builder pytest tests/
```

## Advanced Configuration

### Resource Limits

Control CPU and memory usage:

```bash
# Set via environment variables
export BUILD_CPUS=4
export BUILD_MEMORY=4G

# Or in docker-compose.yml
docker-compose run --cpus=4 --memory=4g builder
```

### Custom LLVM Version

Build with a different LLVM version:

```bash
docker build --build-arg LLVM_VERSION=17 -t feuerbird-builder:llvm17 .
```

### Enable KVM for QEMU

For hardware-accelerated QEMU testing:

```bash
docker run --rm --device /dev/kvm:/dev/kvm \
  -v $(pwd):/workspace feuerbird-builder \
  qemu-system-x86_64 -enable-kvm -kernel build/kernel
```

### Persistent Build Cache

Use named volumes for faster rebuilds:

```bash
docker volume create feuerbird-build-cache

docker run --rm \
  -v $(pwd):/workspace \
  -v feuerbird-build-cache:/build \
  feuerbird-builder
```

## Performance Optimization

### Build Speed Tips

1. **Use BuildKit**: `export DOCKER_BUILDKIT=1` before building
2. **Parallel Builds**: Automatically uses all CPUs via `-j$(nproc)`
3. **Layer Caching**: `.dockerignore` excludes unnecessary files
4. **Volume Mounts**: Use volumes for build artifacts to avoid copying

### Expected Performance

On a typical development machine:

- **Image Build Time**: ~5-10 minutes (first time), ~30 seconds (cached)
- **Kernel Build Time**: ~2-5 minutes (depending on configuration)
- **Container Startup**: < 1 second

### Benchmark Results

Run the benchmark to measure performance on your system:

```bash
./scripts/docker-build.sh benchmark
```

Example output:
```
[INFO] Benchmarking CMake build (cold cache)...
cmake configuration: 15.2s
ninja build: 145.8s
✅ Benchmark completed in 161 seconds
```

## Troubleshooting

### Docker Not Found

```bash
# Install Docker
curl -fsSL https://get.docker.com -o get-docker.sh
sh get-docker.sh
```

### Permission Denied

```bash
# Add user to docker group
sudo usermod -aG docker $USER
newgrp docker
```

### Out of Disk Space

```bash
# Clean up unused containers and images
docker system prune -a

# Clean up volumes
docker volume prune
```

### Build Cache Issues

```bash
# Force rebuild without cache
docker build --no-cache -t feuerbird-builder .

# Clear build cache
docker builder prune
```

### Slow Builds

- Enable BuildKit: `export DOCKER_BUILDKIT=1`
- Use SSD storage for Docker images
- Increase Docker memory limit in Docker Desktop settings
- Check `.dockerignore` to ensure large files are excluded

## CI/CD Integration

### GitHub Actions

The container is designed to work seamlessly with GitHub Actions:

```yaml
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Build container
        run: docker build -t feuerbird-builder .
      - name: Build kernel
        run: docker run --rm -v $PWD:/workspace feuerbird-builder
               bash -c "cmake -B build -G Ninja && ninja -C build"
```

### GitLab CI

```yaml
build:
  image: docker:latest
  services:
    - docker:dind
  script:
    - docker build -t feuerbird-builder .
    - docker run --rm -v $PWD:/workspace feuerbird-builder
        bash -c "cmake -B build -G Ninja && ninja -C build"
```

## Container Architecture

### Multi-Stage Build

```
┌─────────────────────────────────────┐
│ Stage 1: builder (Full Dev Env)    │
│ - Ubuntu 24.04 LTS                  │
│ - LLVM 18 toolchain                 │
│ - All build tools                   │
│ - Development utilities             │
│ Size: ~2.5 GB                       │
└─────────────────────────────────────┘
            │
            ▼
┌─────────────────────────────────────┐
│ Stage 2: runtime (Minimal)          │
│ - Ubuntu 24.04 LTS                  │
│ - QEMU only                         │
│ - No build tools                    │
│ Size: ~500 MB                       │
└─────────────────────────────────────┘
```

### Directory Structure

```
/workspace          # Source code (mounted from host)
/build              # Build artifacts (can be volume)
/home/builder       # User home directory
```

## Security Considerations

1. **Non-root User**: Builds run as UID 1000 `builder` user
2. **Minimal Privileges**: No unnecessary capabilities
3. **Read-only Mounts**: Use `:ro` for read-only source access
4. **Updated Base**: Ubuntu 24.04 with latest security patches
5. **No Secrets**: Never embed secrets in container images

## Comparison with Native Builds

| Aspect            | Native Build    | Container Build |
|-------------------|-----------------|-----------------|
| Setup Time        | 30-60 minutes   | 5-10 minutes    |
| Consistency       | Variable        | 100% consistent |
| Isolation         | None            | Full isolation  |
| Portability       | OS-dependent    | Works anywhere  |
| Build Speed       | Fastest         | ~5% slower      |
| Disk Space        | ~2 GB           | ~2.5 GB         |

## Best Practices

1. **Volume Mounts**: Always mount source as volume, don't copy into image
2. **Named Volumes**: Use named volumes for build cache persistence
3. **Resource Limits**: Set appropriate CPU/memory limits
4. **Regular Updates**: Rebuild image monthly for security updates
5. **Version Tags**: Tag images with dates for reproducibility
6. **Layer Optimization**: Combine related RUN commands to minimize layers

## Future Enhancements

- [ ] ARM64 native image support
- [ ] Pre-built images on Docker Hub
- [ ] Nix-based alternative for reproducibility
- [ ] Remote caching with BuildKit
- [ ] Integration with Bazel build system

## References

- [Docker Best Practices](https://docs.docker.com/develop/dev-best-practices/)
- [BuildKit Documentation](https://docs.docker.com/build/buildkit/)
- [LLVM Docker Images](https://github.com/ClangBuiltLinux/dockerimage)
- [Multi-stage Builds](https://docs.docker.com/build/building/multi-stage/)

## Support

For issues or questions about the container build environment:

1. Check this documentation
2. Run `./scripts/docker-build.sh info` for diagnostics
3. Review GitHub Actions logs for CI issues
4. Open an issue on GitHub

---

**Container Build Environment Version**: 1.0.0  
**Last Updated**: 2024-12-29  
**Maintainer**: FeuerBird Exokernel Project
