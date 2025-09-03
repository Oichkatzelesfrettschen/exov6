# Outline of Analytical Performance Bounds for FeuerBird

## 1. Introduction

### Purpose
This document provides an initial analytical performance model, primarily using Big O notation, for key operations within FeuerBird's formally specified domain security lattice, capability delegation algebra, and vector timestamp protocol. The aim is to establish a theoretical understanding of the computational complexity associated with these core security mechanisms.

### Goal
These preliminary performance bounds serve multiple purposes:
- Act as design constraints during the implementation phase.
- Aid in reasoning about the scalability and efficiency of the system as the number of domains, capabilities, or other relevant parameters grow.
- Provide a basis for comparing different implementation choices for underlying data structures and algorithms.
- Help in identifying potential performance bottlenecks early in the design cycle.

This document focuses on the computational complexity based on the abstract data structures and operations defined in the formal specifications. Empirical performance will depend on concrete implementations, hardware, and specific workloads.

## 2. Notation and Assumptions

The following notation and assumptions are used throughout this analysis:

- **`N_caps`**: Total number of capability slots in the system (e.g., `CAP_MAX` from `include/cap.h`). This represents the maximum number of capabilities that can exist concurrently.
- **`N_dom`**: Number of security domains actively participating in the vector timestamp system. This is the dimension of the vector timestamps.
- **`K_avg`**, **`K_max`**: Average and maximum number of categories associated with a domain's security level `L(d).cats`.
- **`|S|`**: Cardinality of a set of domains `S`.
- **Rights Representation**: Rights are assumed to be represented as bitmasks fitting within one or a small constant number of machine words. Therefore, bitwise operations on rights (AND, OR, XOR, check bit) are considered O(1).
- **Category Set Operations**: Operations on category sets (subset check `⊆`, union `∪`, intersection `∩`) associated with domain security levels are assumed to be performed on sets of size up to `K_max`. The complexity depends on the representation:
    - If `K_max` is small and fixed (e.g., categories can be mapped to bits in a machine word), these can be O(1).
    - If using more general set representations (e.g., hash sets or sorted lists/arrays), operations could be O(K_max) on average or worst-case. For this analysis, we will use **O(K_max)** as a general bound for category set operations, noting it can approach O(1) if `K_max` is small and bitmask-optimizable.
- **`cap_table` Access**: The main capability table (`cap_table` in `kernel/cap_table.c`) is assumed to be a direct-access array, where lookup of a capability by its index (derived from the lower bits of a capability ID) is O(1).
- **Standard CPU Operations**: Basic arithmetic, logical operations, and memory accesses are assumed to be O(1).

## 3. Performance Bounds

### 3.1. Domain Lattice Operations

These operations involve comparing or combining the security levels `L(d) = (cls, cats)` of domains.

- **`LatticeLeq(d1, d2)`** (Compare security levels of two domains `d1` and `d2`):
    - Classification comparison (`L(d1).cls ≤ L(d2).cls`): O(1).
    - Category set subset check (`L(d1).cats ⊆ L(d2).cats`): O(K_max) in the general case (e.g., iterating through `L(d1).cats` and checking for presence in `L(d2).cats`).
    - **Overall Complexity: O(K_max)**.
    - *Note*: If `K_max` is small enough to be represented by a bitmask (e.g., < 64 categories), this operation can become O(1).

- **`LatticeLub(d1, d2)` / `LatticeGlb(d1, d2)`** (Join/Meet of two domains `d1` and `d2`):
    - `max(L(d1).cls, L(d2).cls)` or `min(L(d1).cls, L(d2).cls)`: O(1).
    - Category set union (`L(d1).cats ∪ L(d2).cats`) or intersection (`L(d1).cats ∩ L(d2).cats`): O(K_max) in the general case.
    - **Overall Complexity: O(K_max)**.
    - *Note*: Approaches O(1) if `K_max` is small and bitmask-optimizable.

- **`LatticeLub(S)` / `LatticeGlb(S)`** (Supremum/Infimum for a set `S` of domains):
    - This involves iteratively applying the pairwise Join/Meet operation over all domains in `S`.
    - If `|S|` is the number of domains in the set `S`.
    - **Overall Complexity: O(|S| * K_max)**.

### 3.2. Delegation Algebra Operations

These operations relate to the creation and validation of capability delegations.

- **`DelegateCapability(c_parent, d_target, r_mask)`**:
    This involves several sub-operations:
    1.  **Rights Check on `c_parent`**: Verifying `DELEGATE_RIGHT ∈ rights(c_parent)`. This is an O(1) bitwise operation.
    2.  **`CanDelegate` Check**: This involves comparing the security levels of the source domain (owner of `c_parent`) and `d_target` using `LatticeLeq`. Complexity: O(K_max).
    3.  **`cap_table_alloc`**: Allocating a new slot for `c_child` in the system capability table.
        -   Current implementation in `kernel/cap_table.c` (as reviewed): Involves a linear scan for a free slot. Complexity: **O(N_caps)**.
        -   Target/Desirable implementation: With optimized free list management (e.g., a linked list of free slots), this could be O(1) on average. If a more structured approach is needed for finding specific types of free slots or due to NUMA considerations, it might be O(log N_caps).
    4.  **Rights Attenuation**: `rights(c_child) = rights(c_parent) ∩ r_mask`. This is an O(1) bitwise operation.
    5.  **VT Update for Source Domain**: If the delegation event itself is considered a local event for the source domain (which it should be), this involves `VTLocalEvent`. Complexity: O(1). (Note: If the capability itself carries a VT that needs updating, that's separate).

    - **Overall Complexity (Current, using linear scan `cap_table_alloc`): O(N_caps + K_max)**.
    - **Overall Complexity (Target, with O(1) `cap_table_alloc`): O(1 + K_max)** (or simply O(K_max) if K_max > 0).
    - **Overall Complexity (Target, with O(log N_caps) `cap_table_alloc`): O(log N_caps + K_max)**.

### 3.3. Vector Timestamp (VT) Operations

These operations assume that domain identifiers can be mapped to vector clock indices in O(1) time (e.g., if domains are numbered `0` to `N_dom-1`).

- **`VTLocalEvent(vt_i, domainIndex_i)`** (Domain `i` increments its local clock `vt_i[i]`):
    - Direct array access and increment.
    - **Overall Complexity: O(1)**.

- **`VTSend(vt_i, domainIndex_i)`** (Domain `i` prepares its VT to send with a message):
    - Includes a `VTLocalEvent` for the send event: O(1).
    - Copying the vector `vt_i` (of size `N_dom`) to attach to the message.
    - **Overall Complexity: O(N_dom)**.

- **`VTReceive(vt_j, vt_msg_received, domainIndex_j)`** (Domain `j` receives `vt_msg_received` and updates `vt_j`):
    - Component-wise MAX operation over `N_dom` elements: `∀k: vt_j[k] = max(vt_j[k], vt_msg_received[k])`. This takes O(N_dom) time.
    - Includes a `VTLocalEvent` for the receive event: O(1).
    - **Overall Complexity: O(N_dom)**.

- **`VTLt(vt1, vt2)`** (Compare two vector timestamps `vt1` and `vt2`):
    - Component-wise comparison over `N_dom` elements.
    - **Overall Complexity: O(N_dom)**.

### 3.4. Epoch Synchronization (Conceptual)

This considers the propagation of epoch updates using the VT protocol.

- **Single Epoch Update Propagation (`dSource` informs `dTarget`)**:
    - `dSource` performs a local event (epoch update, `VTSLocalEvent`): O(1).
    - `dSource` prepares and sends the VT with the message (`VTSend`): O(N_dom).
    - `dTarget` receives the message and updates its VT (`VTReceive`): O(N_dom).
    - **Overall Complexity: O(N_dom)** (dominated by send/receive of the vector).

- **Cascade to `M` recipient domains (e.g., one source informs M other domains)**:
    - If this involves `M` separate send/receive pairs, each taking O(N_dom).
    - **Overall Complexity: O(M * N_dom)**.

### 3.5. Core Capability Table Operations (from `kernel/cap_table.c`)

These are based on the current implementation as reviewed.

- **`cap_table_alloc()`**:
    - Current implementation: Linear scan for a free slot.
    - **Overall Complexity: O(N_caps)**.
    - Target/Desirable: O(1) average (with a simple free list head pointer) or O(log N_caps) (e.g., if using a balanced tree of free lists for more complex allocation strategies, though unlikely for this structure).

- **`cap_table_lookup(id, *out)`**:
    - Deriving index from `id`: O(1).
    - Direct array access `cap_table[idx]`: O(1).
    - Epoch comparison: O(1).
    - **Overall Complexity: O(1)**.

- **`cap_revoke(id)`** (Direct, non-transitive revocation as currently implemented):
    - Involves `cap_table_lookup` (effectively O(1)) to find the entry.
    - Modifying the entry (incrementing epoch, setting type to `CAP_TYPE_NONE`): O(1).
    - **Overall Complexity: O(1)**.

## 4. Summary Table of Key Operations and Bounds

| Operation                                  | Current/Estimated Bound      | Target/Board Expectation      | Notes                                                        |
|--------------------------------------------|------------------------------|-------------------------------|--------------------------------------------------------------|
| `LatticeLeq(d1,d2)`                       | O(K_max)                     | O(K_max) or O(1)              | If K_max small & bitmaskable, effectively O(1)             |
| `LatticeLub(d1,d2)` / `LatticeGlb(d1,d2)`  | O(K_max)                     | O(K_max) or O(1)              | If K_max small & bitmaskable, effectively O(1)             |
| `LatticeLub(S)` / `LatticeGlb(S)`          | O(|S| * K_max)              | O(|S| * K_max)                 | For a set S of domains                                       |
| `DelegateCapability`                     | O(N_caps + K_max)            | O(log N_caps + K_max) or O(1+K_max) | Dominated by current `cap_table_alloc`                       |
| `VTLocalEvent`                             | O(1)                         | O(1)                          | Single component update                                      |
| `VTSend`                                   | O(N_dom)                     | O(N_dom)                      | Copying vector                                               |
| `VTReceive`                                | O(N_dom)                     | O(N_dom)                      | Component-wise MAX + local event                             |
| `VTLt` (VT comparison)                   | O(N_dom)                     | O(N_dom)                      | Linear in number of domains for vector ops                   |
| Epoch Sync (1 source to 1 target)        | O(N_dom)                     | O(N_dom)                      | Dominated by VT send/receive                                 |
| `cap_table_alloc`                        | O(N_caps)                    | O(log N_caps) or O(1) avg   | Current is linear scan; target is optimized free list        |
| `cap_table_lookup`                       | O(1)                         | O(1)                          | Current is direct array access + epoch check                 |
| `cap_revoke` (direct)                    | O(1)                         | O(1)                          | Direct modification                                          |

*Note on `cap_table_lookup` Target*: While the current implementation is O(1), the "Board Expectation" from some requirements might imply a more complex underlying structure for capabilities (e.g., if IDs were not direct indices or if capabilities were stored in a tree for other reasons). For the current `cap_table.c` array structure, O(1) is accurate.

## 5. Pedagogical Implications and Design Constraints

- **Scalability Concerns**: Operations with complexity O(N_dom) (Vector Timestamp operations, Epoch Synchronization) or O(N_caps) (current `cap_table_alloc`) are critical bottlenecks as the number of domains or total capabilities increases. These highlight areas where the system's scale might be limited or where performance degradation could occur.
- **Parameter Impact**: The parameters `N_dom`, `N_caps`, and `K_max` are key drivers of performance.
    - A large `N_dom` directly impacts VT operations. This might constrain the number of active, independent security domains that frequently exchange causally ordered messages.
    - A large `N_caps` impacts the current `cap_table_alloc`. Improving this is essential for systems that frequently create/destroy capabilities.
    - `K_max` affects lattice operations; keeping the number of categories per domain manageable (or using efficient bitmask representations if feasible) is important for fast security policy checks.
- **Design Choices**: The desire for O(1) or O(log N) complexity for frequent operations (like capability allocation, lookup, and basic lattice checks) strongly motivates the selection of efficient data structures (e.g., hash tables, balanced trees, efficient free lists) and algorithms in the concrete implementation.
- **Trade-offs**: There's often a trade-off between the richness of the security model (e.g., many categories, many dynamic domains) and the performance of its core operations. These analytical bounds help quantify these trade-offs.

## 6. Future Work

- **Concrete Data Structures**: Refine these bounds once concrete data structures for representing category sets, managing free capability slots, and potentially mapping domain IDs to VT indices are chosen for the C17 implementation.
- **Average-Case and Amortized Analysis**: For operations involving dynamic data structures (e.g., hash tables for category sets, optimized free lists), average-case or amortized analysis might provide a more typical performance expectation than worst-case.
- **Space Complexity**: Analyze the space complexity of these structures (e.g., VTs require O(N_dom) per domain, GDTs, page tables, capability table itself).
- **Contention Modeling**: For operations requiring locks (e.g., `cap_table_alloc`), model performance under contention in a multi-core environment.
- **Empirical Validation**: Ultimately, these analytical bounds should be validated through benchmarking and profiling of the actual FeuerBird implementation.
