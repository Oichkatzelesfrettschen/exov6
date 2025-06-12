# Formal Domain Lattice Specification for FeuerBird

## 1. Introduction

### Purpose
This document defines a formal security lattice for the FeuerBird Operating System. The lattice provides a mathematical framework to govern information flow and control authority between different security domains within the system. It aims to establish a clear, provable basis for enforcing security policies.

### Scope
This initial model focuses on a foundational set of domains:
- A **System Domain** representing the kernel and highest privilege.
- A set of **Process Domains**, one for each active process.
- A **Null Domain** representing no privilege or the lowest authority.

Future extensions may incorporate more granular domains, such as those for specific resources or finer-grained kernel components.

## 2. Domain Definition (D)

The set of security domains `D` in FeuerBird is composed of the following elements:

- **`D_K` (System Domain)**: This domain represents the FeuerBird kernel, operating at the highest privilege level. It is the ultimate authority in the system.
- **`D_P` (Set of Process Domains)**: For each active process `p` in the system, there exists a corresponding security domain `D_p`.
- **`D_∅` (Null Domain)**: This domain represents the complete absence of privilege or authority. It serves as the bottom element of the lattice.

Thus, the complete set of domains is:
`D = {D_K, D_∅} ∪ {D_p | p is a process}`.

### Security Level `L(d)`
Each domain `d ∈ D` is assigned a security level `L(d)`. This security level is a tuple `(cls, cats)` where:

- **`cls` (Classification)**: An element from a totally ordered set `Classifications`. This represents the hierarchical security level or integrity level of the domain. For simplicity, these can be represented by integers, where a higher value indicates a higher classification. For example:
    - `User_Untrusted = 0`
    - `User_Standard = 1`
    - `User_Privileged = 2`
    - `Supervisor = 3` (e.g., for drivers or special system services)
    - `Kernel = 4`
    So, `L(d).cls ∈ {0, 1, 2, 3, 4}`.

- **`cats` (Categories)**: A set of symbolic tags representing non-hierarchical compartments, resource types, or specific access rights associated with the domain. These categories are drawn from a finite set `AllCats`. For example:
    - `AllCats = {FS_READ, FS_WRITE, NET_ACCESS, IPC_SEND, IPC_RECEIVE, CRYPTO_KEY_ACCESS, HW_ACCESS_X}`.
    - `L(d).cats ⊆ AllCats`.

## 3. Partial Order Relation (≤)

A partial order relation `≤` (read as "is subordinate to" or "can flow to") is defined on the set of domains `D`. For any two domains `d1, d2 ∈ D`, `d1 ≤ d2` if and only if their security levels satisfy the following conditions:

`L(d1).cls ≤ L(d2).cls`   (The classification of `d1` is less than or equal to the classification of `d2`)
**AND**
`L(d1).cats ⊆ L(d2).cats` (The set of categories of `d1` is a subset of or equal to the set of categories of `d2`)

This definition means that information is permitted to flow from `d1` to `d2` (or `d1` has less or equal privilege/authority compared to `d2`).

### Properties
The relation `≤` as defined above forms a valid partial order because it satisfies:
- **Reflexivity**: For any `d ∈ D`, `d ≤ d` because `L(d).cls ≤ L(d).cls` and `L(d).cats ⊆ L(d).cats`.
- **Antisymmetry**: If `d1 ≤ d2` and `d2 ≤ d1`, then `L(d1).cls ≤ L(d2).cls` and `L(d2).cls ≤ L(d1).cls`, implying `L(d1).cls = L(d2).cls`. Also, `L(d1).cats ⊆ L(d2).cats` and `L(d2).cats ⊆ L(d1).cats`, implying `L(d1).cats = L(d2).cats`. Thus, `L(d1) = L(d2)`, meaning `d1 = d2` (assuming domains are uniquely defined by their security levels, or this defines equivalence classes).
- **Transitivity**: If `d1 ≤ d2` and `d2 ≤ d3`, then `L(d1).cls ≤ L(d2).cls` and `L(d2).cls ≤ L(d3).cls`, so `L(d1).cls ≤ L(d3).cls`. Also, `L(d1).cats ⊆ L(d2).cats` and `L(d2).cats ⊆ L(d3).cats`, so `L(d1).cats ⊆ L(d3).cats`. Therefore, `d1 ≤ d3`.

## 4. Lattice Operations (Join ⊔ and Meet ⊓)

The partially ordered set `⟨D, ≤⟩` forms a lattice with the following join and meet operations:

### Join (`d1 ⊔ d2`) - Least Upper Bound (LUB)
The join of two domains `d1` and `d2`, denoted `d1 ⊔ d2`, represents the minimal security level that encompasses both `d1` and `d2`. Its security level is defined as:

`L(d1 ⊔ d2) = (max(L(d1).cls, L(d2).cls), L(d1).cats ∪ L(d2).cats)`

This operation is used to determine the required security level for an entity that needs to interact with or access resources from both `d1` and `d2`.

### Meet (`d1 ⊓ d2`) - Greatest Lower Bound (GLB)
The meet of two domains `d1` and `d2`, denoted `d1 ⊓ d2`, represents the maximal security level that is common to both `d1` and `d2`. Its security level is defined as:

`L(d1 ⊓ d2) = (min(L(d1).cls, L(d2).cls), L(d1).cats ∩ L(d2).cats)`

This operation can be used to find the shared level of trust or access rights between two domains.

## 5. Proof of Complete Lattice

To show that `⟨D, ≤⟩` is a complete lattice, we must demonstrate that every subset of `D` has a supremum (Least Upper Bound, LUB) and an infimum (Greatest Lower Bound, GLB), which includes the existence of a global top (⊤) and bottom (⊥) element.

### Top Element (⊤)
The top element of the lattice is the System Domain `D_K`. Its security level is defined as:
`L(D_K) = (max_classification_value, AllCats)`
where `max_classification_value` is the highest possible classification (e.g., `Kernel = 4`) and `AllCats` is the set of all possible categories.

For any domain `d ∈ D`:
- `L(d).cls ≤ max_classification_value = L(D_K).cls`
- `L(d).cats ⊆ AllCats = L(D_K).cats`
Therefore, `∀d ∈ D: d ≤ D_K`.

### Bottom Element (⊥)
The bottom element of the lattice is the Null Domain `D_∅`. Its security level is defined as:
`L(D_∅) = (min_classification_value, ∅)`
where `min_classification_value` is the lowest possible classification (e.g., `User_Untrusted = 0`) and `∅` is the empty set of categories.

For any domain `d ∈ D`:
- `min_classification_value ≤ L(d).cls` which means `L(D_∅).cls ≤ L(d).cls`
- `∅ ⊆ L(d).cats` which means `L(D_∅).cats ⊆ L(d).cats`
Therefore, `∀d ∈ D: D_∅ ≤ d`.

### Completeness
For any arbitrary subset `S ⊆ D`:

- **Supremum (`⊔S`)**: The LUB of `S` is a domain whose security level `L(⊔S)` is defined as:
  `L(⊔S) = (max_{d∈S}(L(d).cls), ∪_{d∈S}(L(d).cats))`
  This exists because the set of classifications is totally ordered and finite (so `max` is well-defined), and the union of category sets is well-defined and results in a subset of `AllCats`.

- **Infimum (`⊓S`)**: The GLB of `S` is a domain whose security level `L(⊓S)` is defined as:
  `L(⊓S) = (min_{d∈S}(L(d).cls), ∩_{d∈S}(L(d).cats))`
  This exists because `min` is well-defined for classifications, and the intersection of category sets is well-defined.

Since every subset `S` of `D` has both a supremum and an infimum within `D` (assuming domains can be constructed for any valid combination of `cls` and `cats` resulting from these operations, or we consider the lattice of security levels themselves), `⟨D, ≤⟩` is a complete lattice.

## 6. Mapping to FeuerBird Concepts

### Process Domains `D_p`
Each active process `p` in FeuerBird, uniquely identified (e.g., by its Process ID or PID), constitutes a distinct security domain `D_p`. The capabilities and resources accessible by a process are determined by the security level `L(D_p)` of its domain.

### Initial Security Levels
- **`D_K` (System Domain)**: `L(D_K) = (Kernel, AllCats)`.
- **`D_∅` (Null Domain)**: `L(D_∅) = (User_Untrusted, ∅)`.
- **Initial Process (`D_init`)**: The first user-space process (e.g., an init daemon or root user shell) could be assigned a default level such as:
  `L(D_init) = (User_Standard, {FS_READ, FS_WRITE, NET_ACCESS, IPC_SEND, IPC_RECEIVE})`.
- **Process Creation**: When a process `D_parent` creates a child process `D_child`, the child's security level is typically derived from the parent. A common policy is that the child cannot have more privileges than the parent:
  `L(D_child).cls ≤ L(D_parent).cls`
  `L(D_child).cats ⊆ L(D_parent).cats`
  The exact mechanism for assigning and potentially restricting these levels upon process creation will be further defined by FeuerBird's capability delegation and process management policies.
- **Kernel-Created Threads/Processes**: Specialized kernel threads or processes (e.g., device drivers if run as separate processes) might be assigned specific classifications like `Supervisor` and a tailored set of categories relevant to their function.

### Role of `D_K`
`D_K` represents the Trusted Computing Base (TCB) of FeuerBird. It is the most privileged domain. Capabilities held or originating from `D_K` are considered system-level capabilities. `D_K` is the ultimate arbiter of security policy and can manage the security levels of other domains.

### Role of `D_∅`
`D_∅` serves as a universal subordinate. It represents a state with no inherent access rights or privileges. Any operation or resource requiring a specific privilege level cannot be accessed by an entity solely in `D_∅`. It forms the baseline from which all other domains derive their relative standing.

## 7. Pedagogical Visualization

The security lattice `⟨D, ≤⟩` can be visualized using **Hasse diagrams**, especially for simpler configurations. For example, a system with `D_K`, `D_∅`, and a few process domains `D_p1`, `D_p2`, `D_p3` with varying security levels can illustrate the flow relationships.

Consider `D_p1` with `L(D_p1) = (User_Standard, {FS_READ})` and `D_p2` with `L(D_p2) = (User_Standard, {FS_READ, NET_ACCESS})`. In this case, `D_p1 ≤ D_p2`.

Such visualizations are powerful tools for understanding and reasoning about information flow control. For instance, the classic **Bell-LaPadula model** policies can be expressed using this lattice:
- **No Read-Up (Simple Security Property)**: A process `D_p` can only read from an object (or domain) `D_o` if `L(D_p) ≥ L(D_o)`.
- **No Write-Down (*-Property)**: A process `D_p` can only write to an object (or domain) `D_o` if `L(D_o) ≥ L(D_p)`. (Note: For integrity, this is often reversed, e.g., Biba's "no write-up").

The lattice structure provides a clear framework for defining and verifying such policies.

## 8. Future Considerations

This initial specification lays the groundwork. Future enhancements and considerations include:
- **Dynamic Security Levels**: Mechanisms for domains (especially process domains) to change their security levels dynamically, subject to system policy and delegation rules.
- **Resource Domains**: Integrating more granular domains for specific resources (e.g., files, sockets, devices) rather than just process-level compartments.
- **Delegation Algebra**: Defining a formal algebra for how capabilities and associated security attributes can be delegated from one domain to another, and how this interacts with the lattice structure.
- **Object Labeling**: Assigning security levels to objects (files, IPC channels, etc.) and enforcing access based on the relationship between the accessing subject's domain level and the object's label.
- **More Complex Classifications/Categories**: Introducing more fine-grained or structured classifications and categories as system complexity grows.

This formal domain lattice is a foundational component for building a robust and verifiable security architecture in FeuerBird.
