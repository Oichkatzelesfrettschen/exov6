# Research on New Security Policies

This document outlines areas for future research and development concerning advanced security policies within the FeuerBird exokernel.

## 1. Dynamic Policy Enforcement

Explore mechanisms for dynamically loading, updating, and enforcing security policies at runtime without requiring a kernel recompilation or reboot. This could involve:

- **Policy Languages:** Investigating domain-specific languages (DSLs) for expressing security policies (e.g., based on Datalog, Prolog, or other declarative approaches).
- **Policy Decision Points (PDP) and Policy Enforcement Points (PEP):** Designing efficient and secure integration of PDPs (where policy decisions are made) and PEPs (where policies are enforced) within the exokernel and LibOS layers.
- **Hot-swapping Policies:** Researching the ability to hot-swap security policies, similar to scheduler hot-swapping, ensuring graceful transitions and maintaining system integrity.

## 2. Fine-Grained Access Control for New Resource Types

Extend the capability system to provide fine-grained access control for new and emerging resource types, beyond traditional memory, disk, and CPU time. This could include:

- **Network Resources:** Capabilities for specific network flows, QoS parameters, or network device features.
- **Hardware Accelerators:** Capabilities for GPUs, FPGAs, or other specialized hardware, allowing secure and controlled sharing.
- **Sensor Data:** Capabilities for accessing and controlling streams of sensor data, with policies for data privacy and integrity.

## 3. Integration of Formal Methods for Policy Verification

Deepen the integration of formal methods (Coq, TLA+) to formally specify and verify the correctness and security properties of new, complex security policies.

- **Policy Specification:** Developing formal specifications for new security policies using languages like TLA+.
- **Automated Verification:** Exploring automated theorem proving or model checking techniques to verify that policy implementations adhere to their specifications.
- **Runtime Monitoring:** Researching techniques for runtime monitoring of policy compliance, potentially using lightweight formal methods or trusted execution environments.

## 4. Secure Multi-Tenancy and Isolation

Investigate advanced isolation techniques to support secure multi-tenancy, where multiple untrusted tenants can share the same underlying hardware with strong security guarantees.

- **Nested Virtualization Security:** Extending the hypervisor capabilities with security policies for nested virtual machines.
- **Side-Channel Attack Mitigation:** Researching and implementing techniques to mitigate side-channel attacks in a multi-tenant exokernel environment.

## 5. Trust Management and Attestation

Explore mechanisms for establishing and maintaining trust within the system, including remote attestation and secure boot processes.

- **Trusted Computing Base (TCB) Minimization:** Continuously striving to minimize the TCB of the exokernel and its critical security components.
- **Attestation Protocols:** Designing and implementing protocols for remote attestation, allowing external parties to verify the integrity of the system.

This research will contribute to making FeuerBird a highly secure and trustworthy platform for diverse and demanding applications.
