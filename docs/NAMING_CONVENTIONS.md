# FeuerBird Exokernel - Naming Conventions

## Project Identity

The project is named **FeuerBird** (German for "fire bird" / phoenix). All code,
targets, and identifiers should use the `feuerbird` prefix.

## Historical Note

Prior to January 2025, the codebase used mixed naming including `phoenix-*` and
`phoenix_*` prefixes. These have been consolidated to `feuerbird-*` as part of
the harmonization effort.

## CMake Targets

### Target Naming Pattern

```
feuerbird-<component>[-<subcomponent>]
```

### Examples

| Target | Purpose |
|--------|---------|
| `feuerbird-architecture` | Architecture abstraction layer |
| `feuerbird-kernel-security` | Kernel security module |
| `feuerbird-kernel-crypto` | Kernel cryptography module |
| `feuerbird-kernel-streams` | Kernel streams module |
| `feuerbird-libos` | Library OS layer |
| `feuerbird-ddekit` | Device Driver Environment Kit |
| `feuerbird-nstr-graph` | NSTR graph library |
| `feuerbird-protocols` | Protocol definitions |
| `feuerbird-simd` | SIMD dispatch library |
| `feuerbird-arch-x86-legacy` | x86 legacy architecture support |
| `feuerbird-arch-x86-modern` | x86 modern (AVX2+) architecture support |

### CMake Helper Functions

Use the project-provided helper functions:

```cmake
# Create executable with standard settings
feuerbird_add_executable(my-executable
    SOURCES src/main.c src/utils.c
    INCLUDES ${CMAKE_CURRENT_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-architecture
)

# Create library with standard settings
feuerbird_add_library(feuerbird-my-library
    STATIC
    SOURCES src/lib.c
    INCLUDES ${CMAKE_CURRENT_SOURCE_DIR}/include
)
```

## Source File Naming

### General Rules

- Use lowercase with underscores: `capability_table.c`
- Prefix exokernel-specific files with `exo_`: `exo_ipc.c`, `exo_mem.c`
- Prefix capability-related files with `cap_`: `cap_security.c`, `cap_mem.c`

### Architecture-Specific Files

```
src/arch/<platform>/<file>.c
src/arch/x86/simd_sse2.c
src/arch/aarch64/simd_neon.c
```

## Header Guards

Use the project-prefixed pattern:

```c
#ifndef FEUERBIRD_<COMPONENT>_<FILE>_H
#define FEUERBIRD_<COMPONENT>_<FILE>_H

// Content

#endif // FEUERBIRD_<COMPONENT>_<FILE>_H
```

Example:
```c
#ifndef FEUERBIRD_KERNEL_CAPABILITY_H
#define FEUERBIRD_KERNEL_CAPABILITY_H
// ...
#endif // FEUERBIRD_KERNEL_CAPABILITY_H
```

## Namespace Prefixes in C

Since C lacks namespaces, use prefixes consistently:

| Prefix | Domain |
|--------|--------|
| `exo_` | Exokernel primitives |
| `cap_` | Capability system |
| `ipc_` | Inter-process communication |
| `msg_` | Message passing |
| `sched_` | Scheduler |
| `vm_` | Virtual memory |
| `fs_` | File system |
| `dev_` | Device drivers |
| `kern_` | Kernel internals |

## Type Naming

### Structs

```c
struct cap_entry { ... };
struct exo_cap { ... };
struct proc { ... };
```

### Typedefs

Use `_t` suffix for typedef'd types:

```c
typedef uint32_t cap_id_t;
typedef struct cap_entry cap_entry_t;
```

## Conan Package

The Conan package is named `feuerbird-exokernel`:

```python
class FeuerBirdExokernelConan(ConanFile):
    name = "feuerbird-exokernel"
```

## Deprecated Names

The following are **deprecated** and should not be used in new code:

| Deprecated | Use Instead |
|------------|-------------|
| `phoenix_*` | `feuerbird_*` |
| `phoenix-*` | `feuerbird-*` |
| `PHOENIX_*` | `FEUERBIRD_*` |

## Migration

If you encounter `phoenix` references in the codebase:

1. Check if it's in active code or archived/documentation
2. For active code: rename to `feuerbird`
3. For documentation: update to reflect new naming
4. For historical references: note the rename in context
