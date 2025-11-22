# Architecture Capability Matrix

This document outlines the support tiers for different architectures in the Phoenix Exokernel.

## Support Tiers

*   **Tier-1**: Fully supported. CI-tested, boots, runs userland.
*   **Tier-2**: Compile, maybe boot. Partial support.
*   **Tier-3**: Concept only. Experimental or stubbed support.

**x86_64 is the reference implementation. All other arches are tier 2 or 3.**

## Architecture Status

| Architecture | Tier | Notes |
| :--- | :--- | :--- |
| **x86_64** | **Tier-1** | Primary development target. Stable. |
| **aarch64** | Tier-2 | Compiles, initial boot support. |
| **arm** | Tier-2 | Legacy 32-bit ARM support. |
| **ppc** | Tier-3 | PowerPC support (conceptual). |
| **mcu** | Tier-3 | Microcontroller target (experimental). |

## Capability Matrix

| Feature | x86_64 | AArch64 | ARMv7 | PowerPC | MCU |
| :--- | :---: | :---: | :---: | :---: | :---: |
| SMP | Y | N | N | N | N |
| RCU supported | Y | N | N | N | N |
| Lock-free IPC guaranteed | Y | N | N | N | N |
| Capability system fully supported | Y | N | N | N | N |
| VFS + MINIXv3 ready | Y | N | N | N | N |
