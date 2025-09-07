# FeuerBird ExoKernel v6: Unified Architecture Vision

## Holistic System Architecture

### Core Philosophy: Synthesis Through Separation
The exokernel paradigm achieves unity through deliberate separation - each zone operates independently yet harmonizes into a greater whole that transcends traditional OS boundaries.

## Three-Zone Harmonic Architecture

### Zone 0: Kernel Core (The Foundation)
- **Purpose**: Pure mechanism, zero policy
- **Components**:
  - Capability authentication (SipHash-2-4 MACs)
  - Protected control transfer
  - Resource multiplexing
  - Hardware abstraction layer (HAL)
- **Synthesis**: Provides the minimal trusted computing base that enables all higher-level abstractions

### Zone 1: LibOS Layer (The Bridge)
- **Purpose**: Policy implementation, POSIX compliance
- **Components**:
  - POSIX-2024 API surface
  - pthread implementation
  - Signal handling
  - Memory management policies
  - Filesystem abstractions
- **Synthesis**: Transforms raw capabilities into familiar abstractions while preserving flexibility

### Zone 2: Application Space (The Expression)
- **Purpose**: Custom policies, specialized abstractions
- **Components**:
  - User programs
  - Custom schedulers
  - Domain-specific libraries
  - Specialized drivers
- **Synthesis**: Enables unprecedented customization while maintaining security

## Unified Component Integration

### 1. Capability System (The Trust Web)
```
Kernel ← Capabilities → LibOS ← Capabilities → Applications
    ↓                      ↓                      ↓
  Hardware              Policies              Innovation
```
- **Unification**: Single capability namespace across all zones
- **Harmonization**: Cryptographic MACs ensure unforgeable trust
- **Elevation**: Beyond traditional access control to fine-grained resource management

### 2. IPC Channel Architecture (The Communication Symphony)
```
Typed Channels ← Cap'n Proto → Message Passing
      ↓              ↓              ↓
   Safety       Efficiency     Flexibility
```
- **Integration**: Type-safe channels with capability-based endpoints
- **Synthesis**: Zero-copy where possible, type-checked always
- **Amplification**: Surpasses traditional IPC in both safety and performance

### 3. Memory Management Hierarchy (The Resource Lattice)
```
Physical Pages → Virtual Memory → Application Heaps
      ↓              ↓                  ↓
  Capabilities    LibOS Policy    Custom Allocators
```
- **Reconciliation**: Physical and virtual realms unified through capabilities
- **Resolution**: Page-level capabilities compose into arbitrary abstractions
- **Transcendence**: Applications can implement custom memory models

### 4. Scheduler Framework (The Temporal Orchestra)
```
CPU Time → Scheduler Interface → Policy Implementations
    ↓             ↓                     ↓
Hardware      Kernel API          User Schedulers
```
- **Flexibility**: Pluggable schedulers (DAG, Beatty, custom)
- **Unity**: Common interface for diverse scheduling policies
- **Innovation**: Applications can implement domain-specific scheduling

## TODO/FIXME/PLACEHOLDER Analysis & Resolution

### Critical Path Items (Immediate)
1. **HAL Completion**
   - [ ] AArch64 implementation (src/arch/aarch64/)
   - [ ] RISC-V skeleton (src/arch/riscv/)
   - [ ] PowerPC restoration (src/arch/ppc/)

2. **Capability System Enhancement**
   - [ ] Dynamic capability table resizing
   - [ ] Capability revocation lists
   - [ ] Delegation chains

3. **IPC Refinement**
   - [ ] Complete Cap'n Proto integration
   - [ ] Implement multicast channels
   - [ ] Add channel persistence

### Integration Items (Near-term)
1. **Memory Subsystem**
   - [ ] NUMA-aware allocation
   - [ ] Huge page support
   - [ ] Memory capability inheritance

2. **Filesystem Abstraction**
   - [ ] Virtual filesystem layer
   - [ ] Network filesystem support
   - [ ] Persistent capability storage

3. **Device Driver Framework**
   - [ ] User-space driver infrastructure
   - [ ] DMA capability management
   - [ ] Interrupt routing to userspace

### Elevation Items (Long-term)
1. **Security Enhancements**
   - [ ] Capability-based sandboxing
   - [ ] Secure enclaves via capabilities
   - [ ] Attestation framework

2. **Performance Optimization**
   - [ ] JIT compilation for system calls
   - [ ] Adaptive scheduling algorithms
   - [ ] Cache-aware data structures

3. **Distributed Capabilities**
   - [ ] Network-transparent capabilities
   - [ ] Distributed shared memory
   - [ ] Cross-machine IPC

## Build System Unification

### CMake Integration Strategy
```cmake
# Unified build for all architectures
add_library(exokernel_hal INTERFACE)
target_sources(exokernel_hal INTERFACE
  $<$<STREQUAL:${CMAKE_SYSTEM_PROCESSOR},x86_64>:src/arch/x86_64/hal/*.c>
  $<$<STREQUAL:${CMAKE_SYSTEM_PROCESSOR},aarch64>:src/arch/aarch64/hal/*.c>
)

# Zone-specific builds
add_library(kernel_zone0 STATIC ${KERNEL_SOURCES})
add_library(libos_zone1 STATIC ${LIBOS_SOURCES})
add_executable(init_zone2 ${USER_SOURCES})

# Capability-linked dependencies
target_link_libraries(libos_zone1 PRIVATE kernel_zone0_caps)
target_link_libraries(init_zone2 PRIVATE libos_zone1_caps)
```

## Testing & Validation Framework

### Multi-level Testing Strategy
1. **Unit Tests**: Individual component validation
2. **Integration Tests**: Cross-zone interaction verification
3. **System Tests**: Full-stack behavior validation
4. **Performance Tests**: Ensuring synthesis doesn't compromise speed
5. **Security Tests**: Capability isolation verification

## Documentation Harmonization

### Unified Documentation Structure
```
docs/
├── architecture/     # System design documents
├── api/             # API references for each zone
├── guides/          # Implementation guides
├── standards/       # POSIX/C17 compliance docs
└── examples/        # Working code examples
```

## Migration Path from Legacy Code

### Phased Modernization
1. **Phase 1**: Type modernization (uint → uint32_t)
2. **Phase 2**: Function signature updates (C17 compliance)
3. **Phase 3**: Assembly to C conversion where possible
4. **Phase 4**: Platform-specific to HAL migration
5. **Phase 5**: Full synthesis and optimization

## Performance Targets

### Unified Metrics
- **Context Switch**: < 1000 cycles (capability-protected)
- **IPC Latency**: < 500 cycles (typed channels)
- **Memory Allocation**: O(1) for common sizes
- **Capability Verification**: < 100 cycles (SipHash)

## Conclusion

This unified architecture transcends traditional OS design by synthesizing:
- **Separation** (exokernel) with **Integration** (unified capabilities)
- **Safety** (type-checked IPC) with **Performance** (zero-copy)
- **Flexibility** (custom policies) with **Compatibility** (POSIX-2024)

The result is a system where the whole truly exceeds the sum of its parts - each component amplifies the others rather than constraining them.