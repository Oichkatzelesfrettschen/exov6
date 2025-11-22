# Architecture Capability Matrix

This document outlines the support tiers for different architectures in the Phoenix Exokernel.

## Support Tiers

*   **Tier-1**: Fully supported. CI-tested, boots, runs userland.
*   **Tier-2**: Compile, maybe boot. Partial support.
*   **Tier-3**: Concept only. Experimental or stubbed support.

## Architecture Status

| Architecture | Tier | Notes |
| :--- | :--- | :--- |
| **x86_64** | **Tier-1** | Primary development target. Stable. |
| **aarch64** | Tier-2 | Compiles, initial boot support. |
| **arm** | Tier-2 | Legacy 32-bit ARM support. |
| **ppc** | Tier-3 | PowerPC support (conceptual). |
| **mcu** | Tier-3 | Microcontroller target (experimental). |
