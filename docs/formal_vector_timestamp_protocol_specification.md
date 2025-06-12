# Initial Vector Timestamp Protocol Specification for FeuerBird

## 1. Introduction

### Purpose
This document defines an initial Vector Timestamp (VT) protocol for the FeuerBird Operating System. The primary purpose of this protocol is to establish a causal ordering of significant events across different security domains within the system. Such events particularly include updates to domain security epochs and operations related to capability management (e.g., delegation, revocation).

### Importance
In a distributed system, or a multi-domain system like FeuerBird where domains operate with a degree of autonomy, understanding the causal relationship between events is crucial for maintaining consistency and correctness. Vector timestamps provide a mechanism to track these relationships, which is fundamental for:
- Consistent hierarchical epoch management (e.g., ensuring child domain epochs correctly reflect changes in parent domain epochs).
- Preventing race conditions and ensuring orderly updates during capability delegation and revocation across domains.
- Debugging and auditing distributed interactions.

## 2. Vector Timestamp (VT) Structure

Let `N` be the number of security domains actively participating in the system that require causal ordering. For this initial specification, `N` can be considered as a fixed, system-wide constant (e.g., `CAP_MAX` if each potential capability owner/process slot is a domain index) or a pre-defined maximum number of concurrently tracked domains. Each participating domain `d_i` (where `i ∈ {1, ..., N}`) is assigned a unique index `i`.

Each domain `d_i` maintains a **vector timestamp** `V_i`. This is an array (or vector) of `N` integers:
`V_i = (v_i[1], v_i[2], ..., v_i[N])`

- `v_i[k]` (an integer) represents domain `d_i`'s knowledge of the logical time (count of relevant causally ordered events) that has occurred at domain `d_k`.
- `v_i[i]` is the local logical clock of domain `d_i` itself. This component **must be non-decreasing** over time.

## 3. Core Operations and VT Update Rules

The protocol is defined by how vector timestamps are initialized and updated during key operations:

### Initialization
When a domain `d_i` is initialized or joins the set of causally tracked domains, its vector clock `V_i` is set to all zeros:
`V_i := (0, 0, ..., 0)`

### Local Event at Domain `d_i`
For any significant local event within domain `d_i` that needs to be causally ordered with respect to other events in the system, `d_i` updates its local logical clock:
1.  `V_i[i] := V_i[i] + 1`

Examples of such significant local events include:
- Advancement of `d_i`'s own security epoch.
- Local modification of a capability owned by `d_i` that might affect its future delegation or use.
- Preparation to send a message that requires causal ordering.

### Sending a Message `m` from Domain `d_i` to Domain `d_j`
When domain `d_i` prepares to send a message `m` to domain `d_j` (where the events of sending and receiving need to be causally ordered, e.g., a message containing a delegated capability or an epoch update notification):

1.  **Local Event Update**: Domain `d_i` first performs the local event update rule for the send event:
    `V_i[i] := V_i[i] + 1`
2.  **Attach Timestamp**: The current vector timestamp `V_i` of domain `d_i` is attached to the message `m`. Let this be `V_msg = V_i`.

### Receiving a Message `m` (with attached timestamp `V_msg`) at Domain `d_j` from Domain `d_i`
When domain `d_j` receives the message `m` (which includes `V_msg` sent by `d_i`):

1.  **Merge Timestamps**: Domain `d_j` updates its own vector clock `V_j` by taking the component-wise maximum with the received timestamp `V_msg`. This ensures `d_j`'s knowledge incorporates `d_i`'s knowledge (and knowledge `d_i` had of other domains) at the time `m` was sent.
    `∀k ∈ {1, ..., N}: V_j[k] := max(V_j[k], V_msg[k])`
2.  **Local Event Update**: Domain `d_j` then performs the local event update rule for the receive event:
    `V_j[j] := V_j[j] + 1`

## 4. Comparison Rule and Happened-Before Relation (→)

Vector timestamps allow for the determination of causal relationships between events. Let event `a` occur at some domain and have an associated vector timestamp `V(a)`, and event `b` occur at some (possibly different) domain with timestamp `V(b)`.

- **Equality**: `V(a) = V(b)` if and only if `∀k ∈ {1, ..., N}: V(a)[k] = V(b)[k]`.
- **Less than or Equal**: `V(a) ≤ V(b)` if and only if `∀k ∈ {1, ..., N}: V(a)[k] ≤ V(b)[k]`.
- **Strictly Less than**: `V(a) < V(b)` if and only if `V(a) ≤ V(b)` AND `∃l ∈ {1, ..., N}: V(a)[l] < V(b)[l]`. (This means `V(a)` is strictly less in at least one component and less than or equal in all others).

Using these comparisons, we define the **Happened-Before Relation (→)**:
- Event `a` is said to have **happened-before** event `b`, denoted `a → b`, if and only if `V(a) < V(b)`. This implies that `a` could have causally affected `b`.

And **Concurrency (||)**:
- Events `a` and `b` are said to be **concurrent**, denoted `a || b`, if and only if `¬(V(a) < V(b))` AND `¬(V(b) < V(a))`. This means there is no causal path from `a` to `b` or from `b` to `a` that can be determined by the vector timestamps.

## 5. Application to Epoch Synchronization in FeuerBird

Vector timestamps are particularly useful for managing epoch updates across domains in a hierarchical or delegated manner.

- **Domain Epochs**: Each security domain `d_i` in FeuerBird maintains a local epoch counter, `E_i`. This epoch is part of a capability's identifier and is used for revocation.
- **Linking VT to Epochs**: A domain `d_i`'s local logical clock component `V_i[i]` should be incremented whenever its local epoch `E_i` is advanced. More strongly, `V_i[i]` can be directly tied to or even be `E_i`, provided `E_i` is only ever incremented. If `E_i` can be reset or managed differently, then `V_i[i]` acts as the primary sequence number for events including epoch changes. For this specification, let's assume `V_i[i]` increments upon an epoch advancement event.

- **Propagating Epoch Updates**:
    - Consider a scenario where `d_parent` (domain `p`) advances its epoch `E_p`. This is a local event, so `V_p[p]` increments.
    - If `d_parent` needs to inform a child domain `d_child` (domain `c`) of this change (e.g., because `d_child`'s epoch or capabilities derived from `d_parent` are affected), `d_parent` sends an "epoch notification" message `m`.
    - This message `m` would contain relevant information (e.g., `d_parent`'s new epoch value `E_p_new`) and would be timestamped with `d_parent`'s current vector clock `V_p` (after `V_p[p]` was incremented for sending). So, `V_msg = V_p`.
    - When `d_child` receives message `m`:
        1. It updates its vector clock: `∀k: V_c[k] := max(V_c[k], V_msg[k])`. Now, `V_c[p]` (child's knowledge of parent's clock) is at least as current as when `m` was sent.
        2. It increments its local clock: `V_c[c] := V_c[c] + 1`.
        3. `d_child` can then process the content of `m` (e.g., `E_p_new`). It might use this information to adjust its own epoch `E_c` according to the system's epoch inheritance rules (e.g., ensuring `E_c` is consistent with or reflects `E_p_new`).

- **Causal Consistency**: If `d_child` receives multiple epoch-related notifications or capability delegations from different domains, the vector timestamps allow `d_child` to establish a causal order among these received events. If message `m1` (with `V_m1`) from `d_A` causally precedes message `m2` (with `V_m2`) from `d_B` (i.e., `m1 → m2`, implying `V_m1 < V_m2`), then `d_child` can potentially infer this order. This is essential for correctly applying updates that might have dependencies.

## 6. Pedagogical Illustration

Consider three domains: `D1`, `D2`, and `D3` (with indices 1, 2, 3 respectively).
Initial state: `V1 = (0,0,0)`, `V2 = (0,0,0)`, `V3 = (0,0,0)`.

1.  **D1 local event (e.g., advances its epoch E1)**:
    - `V1[1] := V1[1] + 1`  => `V1 = (1,0,0)`.
2.  **D1 sends a message `m1` (e.g., containing a delegated capability or E1 update) to D2**:
    - (Implicit local event for send, if not already covered by epoch advance) `V1[1] := V1[1] + 1`. If already done, `V1` remains `(1,0,0)`. For simplicity, let's assume the epoch advance *was* the send trigger.
    - Message `m1` carries `V_msg1 = (1,0,0)`.
3.  **D2 receives message `m1`**:
    - `V2_before_max = V2 = (0,0,0)`.
    - `V2[k] := max(V2[k], V_msg1[k])` for k=1,2,3:
        - `V2[1] = max(0, 1) = 1`
        - `V2[2] = max(0, 0) = 0`
        - `V2[3] = max(0, 0) = 0`
        - So, `V2` becomes `(1,0,0)`.
    - D2 local event for receive: `V2[2] := V2[2] + 1` => `V2 = (1,1,0)`.
4.  **D2 local event (e.g., advances its epoch E2)**:
    - `V2[2] := V2[2] + 1` => `V2 = (1,2,0)`.
5.  **D2 sends a message `m2` to D3**:
    - Message `m2` carries `V_msg2 = (1,2,0)`.
6.  **D3 receives message `m2`**:
    - `V3_before_max = V3 = (0,0,0)`.
    - `V3[k] := max(V3[k], V_msg2[k])` for k=1,2,3:
        - `V3[1] = max(0, 1) = 1`
        - `V3[2] = max(0, 2) = 2`
        - `V3[3] = max(0, 0) = 0`
        - So, `V3` becomes `(1,2,0)`.
    - D3 local event for receive: `V3[3] := V3[3] + 1` => `V3 = (1,2,1)`.

**Analysis from D3's perspective (`V3 = (1,2,1)`)**:
- `V3[1] = 1`: D3 knows of events up to logical time 1 at D1.
- `V3[2] = 2`: D3 knows of events up to logical time 2 at D2.
- `V3[3] = 1`: D3 is at its own logical time 1.

If D3 later receives a message from D1 with `V_msg_from_D1 = (X,Y,Z)`, and `X ≤ V3[1]` (i.e., `X ≤ 1`), D3 knows it has already seen or incorporated the state of D1 that this message represents (or a later state).

## 7. Initial Scope and Future Considerations

- **Number of Domains (N)**:
    - In this initial specification, `N` (the size of the vector) is assumed to be fixed or correspond to a system-wide maximum number of domains (e.g., max processes).
    - **Dynamic N**: Handling dynamic creation and destruction of domains (processes) requires mechanisms to dynamically grow/shrink vector clocks or use alternative schemes, which are not covered here. This is a significant complexity.

- **Storage of Vector Timestamps**:
    - Each domain `d_i` must persistently store its own vector timestamp `V_i`.
    - For certain synchronization schemes, particularly involving capability validation or revocation based on epochs, it might be necessary for capabilities themselves to carry the vector timestamp (or at least the local clock component) of their granting domain at the moment of delegation.

- **Efficiency and Scalability**:
    - Standard vector timestamps have a size proportional to `N`. If `N` is very large (e.g., thousands of short-lived processes), the overhead of storing and transmitting these vectors can be substantial.
    - Future work might explore optimizations like sparse vectors (only storing entries for domains with which interaction has occurred) or more advanced clock mechanisms like interval tree clocks if scalability becomes a major concern.

- **Fault Tolerance**:
    - This specification implicitly assumes reliable, ordered message delivery between domains for the VT protocol to work as described.
    - Handling lost messages, domain failures, or network partitions would require more robust fault-tolerant distributed algorithms, which are beyond this initial scope.

- **Granularity of Events**:
    - The definition of a "significant local event" that triggers `V_i[i]++` needs to be carefully chosen. Overly frequent increments can lead to large clock values quickly, while too infrequent increments might not capture all necessary causal dependencies. It should primarily relate to events that modify state shared or visible to other domains, or that are part of a sequence whose order matters (like epoch updates).
