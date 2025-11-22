# Phoenix Exokernel Threat Model & Security Architecture

## 1. Introduction

This document defines the threat model and security architecture for the Phoenix Exokernel. It reconciles the high-level Probabilistic DAG Algebra with Capabilities (PDAC) logic with the concrete post-quantum cryptographic implementations used to secure the kernel, LibOS, and user-space boundaries.

## 2. System Architecture & Trust Boundaries

The Phoenix Exokernel minimizes the Trusted Computing Base (TCB) to ensure that security failures in application logic or high-level abstractions do not compromise the entire system.

### 2.1 Trusted Computing Base (TCB)
The TCB consists strictly of components where a compromise effectively grants full system control:
* **The Kernel (`/kernel`)**: Running in Ring 0. Responsible for multiplexing resources securely via capabilities and verifying post-quantum cryptographic signatures.
* **Bootloader**: Responsible for loading the kernel via an integrity-checked chain of trust.
* **Hardware Platform**: CPU, Memory, and IOMMU (where applicable).

### 2.2 Untrusted Components
* **LibOS Layer**: Running in user-space (Ring 3). In this architecture, the POSIX compatibility layer is **untrusted**. It translates POSIX calls to capability operations; a compromise here is confined to the specific process.
* **User Applications**: Arbitrary code execution in Ring 3.
* **Device Drivers (User-space)**: Drivers running outside Ring 0 are considered untrusted.
* **Filesystem Images**: Disk contents are untrusted until verified.

### 2.3 Security Boundaries
The system enforces three primary security boundaries:

1.  **Kernel ↔ LibOS (Ring 0/3 Boundary)**
    * **Mechanism:** System Calls (`syscall`) with strict capability validation.
    * **Enforcement:** All syscalls validate capability rights before execution. Capabilities include type information to prevent "confused deputy" attacks.
    
2.  **Process ↔ Process**
    * **Mechanism:** Hardware memory protection (paging) and Capability access control.
    * **Enforcement:** Processes cannot access each other's memory or handles unless explicitly shared via authenticated IPC.

3.  **LibOS ↔ User App**
    * **Mechanism:** Software abstraction.
    * **Enforcement:** The LibOS provides a sanitization layer but shares the same address space as the app.

---

## 3. Cryptographic Architecture (Post-Quantum)

The system implements a three-layer security architecture using post-quantum primitives to secure the TCB.

### 3.1 Capability System Security (`kernel/cap.c`, `kernel/cap_security.c`)

**Problem:** Previous implementations relied on hardcoded secrets or simple XOR, vulnerable to source code leaks or timing attacks.

**Solution:**
* **Per-boot Secret Derivation:** Capability secrets are derived using HKDF (HMAC-based Key Derivation Function) with multiple entropy sources.
* **Constant-Time Verification:** Prevents timing attacks during capability tag validation.
* **Secure Memory:** Sensitive cryptographic material is explicitly erased (`memset`) after use.

```c
// Secure capability verification (constant-time)
int cap_verify(exo_cap c) {
    hash256_t h;
    compute_tag(c.id, c.rights, c.owner, &h);
    return cap_verify_constant_time(&h, &c.auth_tag);
}
````

### 3.2 Post-Quantum Lattice IPC (`kernel/lattice_ipc.c`)

**Problem:** Unauthenticated IPC is vulnerable to tampering and replay attacks.

**Solution:**

  * **Message Authentication:** Every message includes an HMAC-like authentication tag.
  * **Replay Protection:** Sequence counters prevent message replay.
  * **Lattice Exchange:** Uses parameters inspired by Kyber/tourmaline lattices for quantum-resistant key exchange.

<!-- end list -->

```c
// Authenticated message sending logic
int lattice_send(lattice_channel_t *chan, const void *buf, size_t len) {
    // 1. Compute Auth Tag (HMAC-like)
    // 2. Mix in channel key
    // 3. Encrypt (XOR + Lattice noise)
    // 4. Send with auth tag attached
}
```

### 3.3 Cryptographic Primitives (`kernel/crypto.c`)

**Solution:**

  * **HKDF-like KDF:** Proper key derivation using extract-and-expand pattern.
  * **SHA-256 based:** Standardized hash construction.
  * **Entropy:** Post-quantum key generation uses multiple entropy sources.

-----

## 4\. Attacker Capabilities & Threat Analysis

We consider the following attacker classes and the specific mitigations implemented to address them.

### 4.1 Attacker Classes

| Attacker Type | Access Level | Capabilities |
| :--- | :--- | :--- |
| **Malicious User / Compromised LibOS** | Ring 3 (User) | • Execute arbitrary instructions.<br>• Invoke syscalls with fuzzing arguments.<br>• Attempt resource exhaustion.<br>• Exploit race conditions. |
| **Network Attacker** | Remote | • Inject arbitrary packets.<br>• Exploit parsing logic in the user-space network stack.<br>*(Mitigated by network stack running in user-space).* |
| **DMA Attacker** | Hardware | • Initiate DMA read/writes to physical RAM.<br>*(Requires IOMMU configuration to mitigate).* |

### 4.2 Threat Mitigations Matrix

#### 1\. Capability Forgery & Privilege Escalation

  * **Threat:** An attacker attempts to fabricate a capability handle to access unauthorized resources (e.g., another process's memory).
  * **Mitigation:** \* **PDAC Logic:** A child process cannot mathematically derive a capability with rights greater than its parent.
      * **HKDF Derivation:** Secrets are generated at boot; user-space cannot guess the tag without the kernel master key.

#### 2\. Timing & Side-Channel Attacks

  * **Threat:** An attacker measures the time taken for a syscall to return to guess the validity of a capability tag.
  * **Mitigation:** **Constant-Time Operations.** All cryptographic comparisons in `kernel/crypto.c` are implemented to execute in constant time regardless of input data.

#### 3\. Replay & Tampering

  * **Threat:** An attacker intercepts an IPC message and attempts to replay it later or modify the payload.
  * **Mitigation:** \* **Authenticated Encryption:** Lattice IPC drops packets with invalid auth tags.
      * **Sequence Counters:** Monotonically increasing counters in IPC headers reject replays.

#### 4\. Quantum Decryption

  * **Threat:** A future adversary with a quantum computer decrypts recorded sessions.
  * **Mitigation:** **Lattice Cryptography.** Key exchange relies on Shortest Vector Problem (SVP) hardness rather than integer factorization.

-----

## 5\. Security Validation

The security improvements are validated by an automated test suite (`test_security_audit.py`).

## 6\. Out of Scope & Future Work

### 6.1 Currently Out of Scope

  * **Physical Attacks:** Cold boot attacks, probing hardware bus.
  * **Complex Side-Channels:** Spectre, Meltdown, and Rowhammer mitigations are currently best-effort.
  * **Social Engineering:** User coercion.

### 6.2 Future Work

1.  **Hardware Entropy:** Integrate with hardware random number generators (RDRAND, TPM).
2.  **Formal Verification:** Use formal methods to verify the PDAC algebra properties.
3.  **Standards Compliance:** Align strictly with finalized NIST Post-Quantum Cryptography standards.
4.  **Performance Optimization:** Optimize crypto operations for kernel throughput without compromising security.

<!-- end list -->

```
```