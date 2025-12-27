# Granular CMake Architecture for FeuerBird Exokernel

## Overview

This document outlines the comprehensive zone-based CMake architecture for the FeuerBird Exokernel project. The architecture provides granular build control, clear dependency management, and modular component organization.

## Architectural Zones

### 1. Core Kernel Zone (`kernel/`)
- **Purpose**: Core exokernel implementation
- **Components**: 
  - Main kernel executable
  - System calls
  - Memory management
  - Process management
  - IPC infrastructure
  - Hardware abstraction
- **CMake Target**: `feuerbird-kernel`
- **Dependencies**: `architecture`, `system-libs`

### 2. Library Operating System Zone (`libos/`)
- **Purpose**: User-level OS services and abstractions
- **Components**:
  - POSIX compatibility layer
  - File system services
  - Network stack
  - Process management APIs
  - Resource accounting
  - Service registration
- **CMake Target**: `feuerbird-libos`
- **Dependencies**: `userland-core`, `protocols`

### 3. Userland Zone (`user/`)
- **Purpose**: User space applications and core libraries
- **Components**:
  - User library (`ulib`)
  - Memory allocator (`umalloc`)
  - Capability library (`caplib`)
  - Channel library (`chan`)
  - Door library (`door`)
  - Math core (`math_core`)
- **CMake Target**: `feuerbird-userland`
- **Dependencies**: `protocols`

### 4. Architecture Zone (`src/arch/`)
- **Purpose**: Architecture-specific implementations
- **Components**:
  - x86 legacy support
  - x86 modern support
  - ARM/AArch64 support
  - PowerPC support
  - MCU support
  - SIMD dispatch
- **CMake Target**: `feuerbird-arch`
- **Dependencies**: None (base layer)

### 5. System Libraries Zone (`src/`)
- **Purpose**: Foundational system libraries
- **Components**:
  - DDEKit (Device Driver Environment Kit)
  - NStr Graph library
  - SIMD dispatch library
- **CMake Target**: `feuerbird-syslibs`
- **Dependencies**: `architecture`

### 6. Tools and Utilities Zone (`tools/`)
- **Purpose**: Build tools and development utilities
- **Components**:
  - FeuerBird metrics
  - Compiler utilities
  - Header graph analyzer
  - File organizer
- **CMake Target**: `feuerbird-tools`
- **Dependencies**: None

### 7. Protocols Zone (`proto/`)
- **Purpose**: Interface definitions and protocol specifications
- **Components**:
  - Cap'n Proto definitions
  - Bison parser specifications
  - Interface headers
- **CMake Target**: `feuerbird-protocols`
- **Dependencies**: None

### 8. Demos Zone (`demos/`)
- **Purpose**: Example applications and demonstrations
- **Components**:
  - Wumpus game
  - Message queue demos
  - Fibonacci calculator
  - Channel demonstrations
  - POSIX compatibility tests
- **CMake Target**: `feuerbird-demos`
- **Dependencies**: `libos`, `userland`

### 9. Tests Zone (`tests/`)
- **Purpose**: Comprehensive test suite
- **Components**:
  - Unit tests
  - Integration tests
  - Performance benchmarks
  - Stress tests
- **CMake Target**: `feuerbird-tests`
- **Dependencies**: All zones

### 10. Formal Verification Zone (`formal/`)
- **Purpose**: Formal verification and specification
- **Components**:
  - Coq proofs
  - TLA+ specifications
  - C model implementations
- **CMake Target**: `feuerbird-formal`
- **Dependencies**: None

### 11. Engine Zone (`engine/`)
- **Purpose**: Core engine components (appears to be duplicated structure)
- **Components**:
  - Kernel mirror
  - User mirror
- **CMake Target**: `feuerbird-engine`
- **Dependencies**: TBD

## Dependency Graph

```
feuerbird-kernel ← feuerbird-arch
                 ← feuerbird-syslibs ← feuerbird-arch
                 ← feuerbird-protocols

feuerbird-libos ← feuerbird-userland ← feuerbird-protocols
                ← feuerbird-protocols

feuerbird-demos ← feuerbird-libos
                ← feuerbird-userland

feuerbird-tests ← ALL ZONES

feuerbird-tools (independent)
feuerbird-formal (independent)
```

## Build Features

### Core Features
- **USE_LTO**: Link Time Optimization
- **USE_LLD**: LLVM LLD linker  
- **USE_POLLY**: LLVM Polly optimizations
- **USE_SIMD**: SIMD instruction support
- **USE_CAPNP**: Cap'n Proto support

### Debug Features
- **ENABLE_ASAN**: AddressSanitizer
- **ENABLE_TSAN**: ThreadSanitizer
- **ENABLE_UBSAN**: UndefinedBehaviorSanitizer
- **IPC_DEBUG**: IPC debug logging

### Platform Features
- **MCU**: Microcontroller target
- **USE_TICKET_LOCK**: Ticket-based spinlocks

## CMake Structure

```
CMakeLists.txt (root)
├── cmake/
│   ├── FeuerBirdConfig.cmake
│   ├── FindLLVMTools.cmake
│   ├── CompilerDetection.cmake
│   └── FeatureDetection.cmake
├── kernel/CMakeLists.txt
├── libos/CMakeLists.txt
├── user/CMakeLists.txt
├── src/
│   ├── arch/CMakeLists.txt
│   ├── ddekit/CMakeLists.txt
│   └── libnstr_graph/CMakeLists.txt
├── tools/CMakeLists.txt
├── proto/CMakeLists.txt
├── demos/CMakeLists.txt
├── tests/CMakeLists.txt
├── formal/CMakeLists.txt
└── engine/CMakeLists.txt
```

## Implementation Strategy

1. **Phase 1**: Core infrastructure and architecture zone
2. **Phase 2**: Kernel and system libraries zones  
3. **Phase 3**: Userland and libos zones
4. **Phase 4**: Tools, demos, and tests zones
5. **Phase 5**: Protocols and formal verification zones
6. **Phase 6**: Integration and optimization