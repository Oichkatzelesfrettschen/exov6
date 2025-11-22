# Phoenix Exokernel Threat Model

## 1. Introduction

This document defines the threat model for the Phoenix Exokernel, specifically focusing on the PDAC (Probabilistic DAG Algebra with Capabilities) security architecture and the interaction between the kernel, LibOS, and user applications.

## 2. System Architecture & Trust Boundaries

### 2.1 Trusted Computing Base (TCB)
The TCB consists strictly of:
*   **The Kernel (`/kernel`)**: Running in Ring 0. Responsible for multiplexing resources securely via capabilities.
*   **Bootloader**: Responsible for loading the kernel integrity-checked.
*   **Hardware Platform**: CPU, Memory, and IOMMU (where applicable).

### 2.2 Untrusted Components
*   **LibOS**: In the Phoenix Exokernel design, the Library OS runs in user-space (Ring 3) linked with the application. It is **untrusted**. A compromise of the LibOS is confined to the specific process and its capabilities.
*   **User Applications**: Arbitrary code execution in Ring 3.
*   **Device Drivers (User-space)**: Drivers running outside Ring 0 are untrusted.
*   **Filesystem Images**: Disk contents are untrusted until verified.

### 2.3 Trust Boundaries
*   **Kernel <-> User (LibOS/App)**: The primary boundary. Enforced via System Calls (`syscall` instruction) and strict validation of arguments.
*   **Process <-> Process**: Enforced by the kernel via memory protection (paging) and capability access control.
*   **CPU <-> Device**: Enforced via IOMMU (if enabled) to prevent DMA attacks.

## 3. Attacker Capabilities

We consider the following attacker classes:

### 3.1 Malicious User Process / Compromised LibOS
*   **Capabilities**:
    *   Execute arbitrary instructions in Ring 3.
    *   Invoke any system call with arbitrary arguments.
    *   Attempt to exhaust resources (CPU, Memory) within its quota.
    *   Attempt to exploit race conditions in kernel syscall handlers.
    *   Collaborate with other malicious processes via IPC.
*   **Goal**: Privilege escalation, denial of service to other processes, data exfiltration from other processes or kernel.

### 3.2 Network Attacker
*   **Capabilities**:
    *   Inject arbitrary packets into the network interface.
*   **Goal**: Exploit vulnerabilities in the network stack (which runs in LibOS or user-space driver).
*   **Mitigation**: Since the network stack is in user-space, a compromise here does not immediately yield kernel control.

### 3.3 Malicious Peripheral (DMA Attacker)
*   **Capabilities**:
    *   Initiate DMA read/write requests to arbitrary physical addresses.
*   **Goal**: Overwrite kernel text/data, read secrets.
*   **Risk**: High if IOMMU is not configured.

## 4. Security Invariants & Goals

### 4.1 Capability Logic
*   **No Privilege Escalation**: A process cannot derive a capability with rights strictly greater than its parent.
*   **No Forgeability**: Cryptographic or logic-based capabilities cannot be forged by user-space.
*   **Revocation Safety**: When a capability is revoked, all derived capabilities must be invalidated immediately (or within a bounded epoch).

### 4.2 Lattice Security
*   **Information Flow**: Data must not flow against the lattice policy (e.g., from High Security to Low Security) unless explicitly declassified.
*   **Dominance Check**: Sender must dominate Receiver (or vice versa, depending on policy) for IPC.

### 4.3 Post-Quantum Security
*   **Goal**: Resistance against attackers with quantum computing capabilities capable of breaking RSA/ECC.
*   **Mechanism**: Usage of Kyber/ML-KEM for key exchange in secure channels.

## 5. Out of Scope
*   **Physical Attacks**: Cold boot attacks, probing hardware bus.
*   **Side-Channels**: While we strive for constant-time crypto, comprehensive micro-architectural side-channel (Spectre, Meltdown, Rowhammer) mitigation is currently best-effort.
*   **Social Engineering**: User coercion.
