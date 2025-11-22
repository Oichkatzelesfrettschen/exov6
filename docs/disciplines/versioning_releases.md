# Versioning and Releases

## Semantic Versioning
The project adheres to [Semantic Versioning 2.0.0](https://semver.org/).

### Format: `MAJOR.MINOR.PATCH`
*   **MAJOR**: Incompatible API changes (e.g., breaking the Syscall ABI).
*   **MINOR**: Backwards-compatible functionality (e.g., new syscalls, new LibOS features).
*   **PATCH**: Backwards-compatible bug fixes.

## Component Versioning

### 1. Kernel ABI (`include/syscall.h`)
The Kernel-LibOS interface is strictly versioned.
*   Changes to `syscall_t` or existing syscall numbers require a MAJOR version bump.
*   New syscalls increment MINOR version.

### 2. LibOS (`libos.a`)
*   The LibOS follows its own versioning track, tied to the POSIX compliance level (e.g., POSIX-2024).

## Release Process

1.  **Feature Freeze**: No new features 1 week before release.
2.  **Release Candidate (RC)**: Tagged `v1.2.0-rc1`.
3.  **Testing**: Full regression suite pass (QEMU, Tier-1 architectures).
4.  **Release**: Tag `v1.2.0`, generate changelog, publish artifacts.
5.  **LTS**: Long Term Support releases are maintained for critical security fixes.
