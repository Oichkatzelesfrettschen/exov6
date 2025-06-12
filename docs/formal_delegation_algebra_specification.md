# Initial Delegation Algebra Specification for FeuerBird

## 1. Introduction

### Purpose
This document formally defines the algebra for capability delegation in the FeuerBird Operating System. It specifies how capabilities, representing access rights to resources, are transferred between different security domains and how their associated rights can be attenuated (reduced) during this process. This algebra is crucial for implementing the principle of least privilege and managing authority flow within the system.

### Relationship to Domain Lattice
This specification builds directly upon the "Formal Domain Lattice Specification for FeuerBird". The security domains and their partial ordering defined in the lattice are fundamental to the rules governing capability delegation.

## 2. Core Components

The delegation algebra involves the following core components:

- **Capabilities (C)**: A capability `c ∈ C` is a token representing authority over a system resource. As defined in `include/cap.h`, a capability (e.g., `struct cap_entry`) typically includes:
    - `type`: The kind of resource or service the capability grants access to (e.g., `CAP_TYPE_PAGE`, `CAP_TYPE_CRYPTOKEY`).
    - `resource`: An identifier for the specific resource instance (e.g., a page frame number, a key ID).
    - `rights`: A bitmask representing the permissions granted by this capability (e.g., read, write, execute, delegate).
    - `owner`: The identifier of the domain `d_source` that currently owns and can exercise this capability.
    - `epoch`: A value used for revocation and preventing use-after-free issues.

- **Domains (D)**: Domains are as defined in the Formal Domain Lattice Specification. Each domain `d ∈ D` (e.g., `D_K`, `D_p`, `D_∅`) has an associated security level `L(d) = (cls, cats)`, where `cls` is its classification and `cats` is its set of categories.

- **Rights (R)**: The set of all possible permission bits that can be associated with a capability. Let `U_R` be the universal set of all possible rights. A specific capability's `rights` field is a subset of `U_R`. The set of all possible rights masks forms a lattice under the subset (`⊆`) and superset (`⊇`) relations, with bitwise AND (`∩`) as the meet operation and bitwise OR (`∪`) as the join operation. For delegation, a key right is `DELEGATE_RIGHT`.

## 3. Delegation Operation (δ)

The core of the delegation algebra is the delegation operation `δ`.

### Signature
The delegation operation `δ` takes a parent capability, a target domain, and a rights mask, and produces a new child capability (if permitted):
`δ: C × D × R → C'`
This can be written as: `c_child = δ(c_parent, d_target, r_mask)`

### Parameters
- `c_parent`: The existing capability being delegated. Let `d_source` be the domain that owns `c_parent` (i.e., `owner(c_parent) = id(d_source)`).
- `d_target`: The target domain to which `c_parent` is being delegated.
- `r_mask`: A bitmask of rights that `d_source` intends to grant to `d_target` for the new `c_child` capability. This mask is used to potentially attenuate the rights of `c_parent`.

### Pre-conditions for Valid Delegation
For a delegation operation `δ(c_parent, d_target, r_mask)` to be valid and for `c_child` to be created, the following conditions must hold:

1.  **Delegation Right**: The `rights` field of `c_parent` must include the `DELEGATE_RIGHT` permission (or a more specific delegation permission if the system defines granular delegation rights).
    `DELEGATE_RIGHT ∈ rights(c_parent)`

2.  **Delegation Permission Policy (Domain Lattice Adherence)**: Delegation of authority from a source domain `d_source` to a target domain `d_target` is permitted if and only if the target domain is subordinate to or at the same level as the source domain in the security lattice.
    `L(d_target) ≤ L(d_source)`
    This means `L(d_target).cls ≤ L(d_source).cls` AND `L(d_target).cats ⊆ L(d_source).cats`. This policy ensures that authority does not flow to more privileged domains.

### Properties of the Delegated Capability (`c_child`)
If the pre-conditions are met, a new capability `c_child` is created and allocated in the capability table with the following properties:

1.  **Type Preservation**: The type of the child capability is the same as the parent.
    `type(c_child) = type(c_parent)`

2.  **Resource Preservation**: The child capability refers to the same underlying system resource or object as the parent.
    `resource(c_child) = resource(c_parent)`

3.  **Rights Attenuation**: The rights of the child capability are the intersection of the parent's rights and the rights specified in `r_mask`. This ensures that the child capability cannot have more rights than the parent, nor more rights than were explicitly requested for delegation via `r_mask`.
    `rights(c_child) = rights(c_parent) ∩ r_mask`
    This implies `rights(c_child) ⊆ rights(c_parent)`.

4.  **Ownership Transfer**: The owner of the child capability is the target domain.
    `owner(c_child) = id(d_target)`

5.  **Epoch Assignment**: `c_child` is assigned a new epoch value upon its creation in the capability table. The specifics of epoch management (e.g., inheritance or fresh assignment) are detailed in a separate Epoch Inheritance and Revocation specification. For now, we assume `epoch(c_child)` is properly initialized.

6.  **(Optional) Parent Tracking**: For auditing or advanced revocation schemes, `c_child` could optionally store an identifier for `c_parent`.
    `parent_id(c_child) = id(c_parent)` (This is a consideration for future implementation).

## 4. Delegation Permission Relation (⊢_δ) as a Partial Order

We can define a relation `⊢_δ` to capture when delegation is permitted between domains.

### Definition
Let `d1 ⊢_δ d2` denote "domain `d2` is permitted to delegate capabilities to domain `d1`."

### Equivalence to Lattice Order
This delegation permission relation is directly determined by the security levels of the domains as defined in the Formal Domain Lattice Specification:
`d1 ⊢_δ d2 ⟺ L(d1) ≤ L(d2)`

In other words, `d2` can delegate to `d1` if `d1` is "lower or equal" in the lattice than `d2`.

### Partial Order Properties
Since the relation `≤` on the set of security levels `L(D)` is a partial order (reflexive, antisymmetric, transitive, as established by the domain lattice properties), the delegation permission relation `⊢_δ` (when viewed as `d_target` can receive from `d_source`) is also a partial order.

- **Reflexivity**: `d ⊢_δ d` (a domain `d` is permitted to delegate to itself). This is true because `L(d) ≤ L(d)`. This allows a domain to create a restricted version of one of its own capabilities for a specific internal task or sub-component.
- **Antisymmetry**: If `d1 ⊢_δ d2` and `d2 ⊢_δ d1`, then `L(d1) ≤ L(d2)` and `L(d2) ≤ L(d1)`. This implies `L(d1) = L(d2)`.
- **Transitivity**: If `d1 ⊢_δ d2` (d2 can delegate to d1, so `L(d1) ≤ L(d2)`) and `d_intermediate ⊢_δ d1` (d1 can delegate to d_intermediate, so `L(d_intermediate) ≤ L(d1)`), then by transitivity of `≤` on security levels, `L(d_intermediate) ≤ L(d2)`. This means `d_intermediate ⊢_δ d2` (d2 can delegate to d_intermediate through d1).
   More directly for the delegation path: if `d_source` can delegate to `d_intermediate` (`L(d_intermediate) ≤ L(d_source)`), and `d_intermediate` can delegate to `d_target` (`L(d_target) ≤ L(d_intermediate)`), then `L(d_target) ≤ L(d_source)`, meaning `d_source` could (from a lattice perspective) delegate directly to `d_target`.

## 5. Preservation of Lattice Structure by Delegation

The pre-condition `L(d_target) ≤ L(d_source)` for the delegation operation `δ(c_parent_owned_by_d_source, d_target, r_mask)` is fundamental. It ensures that capabilities, and therefore the authority they represent, flow downwards (to less privileged domains) or laterally (to domains of equal privilege) within the security lattice. Capabilities are not permitted to be delegated upwards to more privileged domains. This strict adherence to the lattice order preserves the integrity of the system's security hierarchy and prevents privilege escalation through delegation.

## 6. Rights Algebra and Monotonicity

### Rights Lattice
The set of all possible rights masks `P(U_R)` (the power set of the universal set of rights `U_R`) forms a Boolean lattice.
- The partial order is set inclusion `⊆`.
- The meet operation (`⊓_R`) is set intersection (`∩`).
- The join operation (`⊔_R`) is set union (`∪`).

### Rights Monotonicity
The rule for determining the rights of a delegated capability is:
`rights(c_child) = rights(c_parent) ∩ r_mask`

This inherently ensures that `rights(c_child) ⊆ rights(c_parent)`. In terms of the rights lattice, `rights(c_child) ≤_R rights(c_parent)`. This property is known as **rights monotonicity** (or non-increasing rights). It is a cornerstone of secure capability systems, guaranteeing that delegation can only restrict rights, never amplify them. The `r_mask` parameter further allows the delegating domain to apply the principle of least privilege by granting only the necessary subset of its own rights.

## 7. Pedagogical Illustration

Consider a simplified scenario with the following domains and security levels:
- `D_K` (Kernel): `L(D_K) = (Kernel_Level, {FS, NET, HW})` (Top of the lattice)
- `D_FM` (File Manager Process): `L(D_FM) = (Supervisor_Level, {FS})`, where `Supervisor_Level < Kernel_Level`.
- `D_UA` (User Application Process): `L(D_UA) = (User_Level, {FS_READ_ONLY})`, where `User_Level < Supervisor_Level` and `{FS_READ_ONLY}` is a conceptual subset of `{FS}` for simplicity (actual rights bits would be used).

Assume `DELEGATE_RIGHT` is implicitly part of the rights being discussed or explicitly included.

**Scenario**:
1.  **Initial Capability**: `D_K` possesses `c_K1` for a file resource, with `rights(c_K1) = {READ, WRITE, DELEGATE_RIGHT}`.

2.  **Delegation 1 (Kernel to File Manager)**:
    `D_K` delegates `c_K1` to `D_FM`.
    - `c_parent = c_K1` (owned by `D_K`)
    - `d_target = D_FM`
    - `r_mask1 = {READ, WRITE, DELEGATE_RIGHT}`
    - **Pre-condition Check**:
        - `DELEGATE_RIGHT ∈ rights(c_K1)` (True)
        - `L(D_FM) ≤ L(D_K)` (True, as `Supervisor_Level < Kernel_Level` and `{FS} ⊆ {FS, NET, HW}` assuming FS is a relevant category within the broader set).
    - **Result**: `c_FM1 = δ(c_K1, D_FM, r_mask1)` is created.
        - `owner(c_FM1) = D_FM`
        - `rights(c_FM1) = rights(c_K1) ∩ r_mask1 = {READ, WRITE, DELEGATE_RIGHT}`

3.  **Delegation 2 (File Manager to User App)**:
    `D_FM` delegates `c_FM1` to `D_UA`.
    - `c_parent = c_FM1` (owned by `D_FM`)
    - `d_target = D_UA`
    - `r_mask2 = {READ}`
    - **Pre-condition Check**:
        - `DELEGATE_RIGHT ∈ rights(c_FM1)` (True)
        - `L(D_UA) ≤ L(D_FM)` (True, as `User_Level < Supervisor_Level` and conceptually `{FS_READ_ONLY}` rights are a restriction of full `{FS}` access).
    - **Result**: `c_UA1 = δ(c_FM1, D_UA, r_mask2)` is created.
        - `owner(c_UA1) = D_UA`
        - `rights(c_UA1) = rights(c_FM1) ∩ r_mask2 = {READ, WRITE, DELEGATE_RIGHT} ∩ {READ} = {READ}`

This example illustrates:
- **Delegation Flow**: Authority flows downwards in the lattice (`D_K` → `D_FM` → `D_UA`).
- **Rights Attenuation**: `rights(c_UA1) = {READ}` is a subset of `rights(c_FM1) = {READ, WRITE, DELEGATE_RIGHT}`. The user application only gets read access, as intended by the file manager.

## 8. Future Considerations

This initial specification of the delegation algebra can be extended in several ways:
- **Revocation of Delegated Capabilities**: Defining how revocation of a parent capability affects its children (e.g., recursive revocation, epoch-based stale capability detection).
- **Limits on Delegation Depth**: Introducing policies to restrict how many times a capability can be re-delegated.
- **Conditional Delegation**: Allowing delegation policies that depend on more complex conditions than just lattice comparison (e.g., specific attributes of the target domain or resource state).
- **Types of Delegation**: Distinguishing between different forms of delegation, such as:
    - **Copy Delegation**: `d_target` receives a new, independent capability.
    - **Loan Delegation**: `d_target` receives a temporary or restricted reference, possibly with the `owner` field still pointing to `d_source` or a proxy.
- **Ambient Authority vs. Capability-Based Authority**: Clarifying how ambient authority derived from a domain's security level interacts with explicitly held capabilities.
- **Integration with IPC**: How capabilities are passed and verified during Inter-Process Communication.

This formal delegation algebra, in conjunction with the domain lattice, provides a robust foundation for managing authority and enforcing security policies in FeuerBird.
