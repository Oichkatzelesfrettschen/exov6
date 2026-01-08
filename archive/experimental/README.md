# Archived Experimental Code

This directory contains experimental implementations that were removed from the
active kernel codebase during the 2025 harmonization effort. These files are
preserved for reference and potential future development.

## Why Archived

These implementations were archived because:

1. **Type conflicts**: Many had conflicting type definitions with the core kernel
2. **Missing dependencies**: Required headers or functions not yet implemented
3. **Architectural overlap**: Multiple implementations of the same concept
4. **Incomplete**: Partial implementations not ready for integration

## Contents

### sync/ - Synchronization Primitives

| File | Description | Status |
|------|-------------|--------|
| quantum_lock.c/h | Quantum-inspired lock using superposition concepts | Incomplete |
| ultimate_lock_*.c/h | Ultimate lock synthesis combining multiple techniques | Type conflicts |
| genetic_lock_evolution.c/h | Genetic algorithm-based lock optimization | Incomplete |
| unified_lock.c/h | Unified lock abstraction layer | Superseded by ticketlock |

### ipc/ - Inter-Process Communication

| File | Description | Status |
|------|-------------|--------|
| quantum_ipc.h | Quantum IPC channel definitions | Incomplete |
| unified_ipc.c | Unified IPC abstraction | Superseded by cap.c |
| unified_channel.c | Channel-based IPC implementation | Superseded |
| zero_copy.c | Zero-copy IPC mechanism | Missing vm.h dependencies |

## Canonical Implementations

The following implementations are now canonical in the kernel:

- **Spinlock**: kernel/spinlock.c (classic + ticketlock option)
- **Sleep lock**: kernel/sleeplock.c
- **IPC**: kernel/ipc/cap.c (capability-based)

## Restoration

To restore any of these implementations:

1. Copy the file back to its original location
2. Resolve any type conflicts with current kernel headers
3. Add to kernel/CMakeLists.txt source list
4. Remove from exclusion patterns in CMakeLists.txt

## Date Archived

2025-01-07 - FeuerBird Harmonization Phase
