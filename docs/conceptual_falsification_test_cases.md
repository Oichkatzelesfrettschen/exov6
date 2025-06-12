# Conceptual Falsification Test Cases for FeuerBird Formal Specifications

## 1. Introduction

### Purpose
This document outlines conceptual test cases designed to probe and potentially falsify (i.e., find violations or inconsistencies in) the key properties and invariants defined in FeuerBird's formal specifications. These specifications currently include:
- Formal Domain Lattice Specification
- Initial Delegation Algebra Specification
- Initial Vector Timestamp Protocol Specification

The goal is not to exhaustively test an implementation, but rather to use these test concepts to refine the formal models themselves and to guide the eventual design of concrete verification and validation test suites for an implementation.

### Methodology
Each test case describes:
- **Property**: The formal property or invariant being tested, derived from the relevant specification.
- **Scenario**: A conceptual sequence of operations or a state configuration.
- **Expected Outcome**: The behavior or result anticipated if the formal property holds true within the scenario.
- **Falsification Condition**: The condition, observation, or result that would indicate a violation of the property, thereby "falsifying" the current understanding or application of the formal model in that scenario.

These test cases are primarily thought experiments at this stage, aimed at uncovering edge cases, ambiguities, or incompleteness in the specifications.

## 2. Domain Lattice Specification Test Cases

Let `L(d)` denote the security level `(cls, cats)` of a domain `d`.
Let `LatticeLeq(L(d1), L(d2))` be the function evaluating `d1 ≤ d2`.

### Test DL.1: Reflexivity (`d ≤ d`)
- **Property**: `∀ d ∈ Domains: d ≤ d`, which means `LatticeLeq(L(d), L(d))` must be true.
- **Scenario**:
    1. Define an arbitrary domain `D_p` with security level `L(D_p) = (cls_p, cats_p)`.
    2. Evaluate `LatticeLeq(L(D_p), L(D_p))`.
- **Expected Outcome**: The evaluation returns `True`.
- **Falsification Condition**: The evaluation `LatticeLeq(L(D_p), L(D_p))` returns `False`. This would indicate a fundamental flaw in the definition of `≤` or its comparison logic.

### Test DL.2: Antisymmetry (`d1 ≤ d2` AND `d2 ≤ d1` => `d1 = d2` in terms of lattice level)
- **Property**: `∀ d1, d2 ∈ Domains: (L(d1) ≤ L(d2) AND L(d2) ≤ L(d1)) ⇒ (L(d1).cls = L(d2).cls AND L(d1).cats = L(d2).cats)`.
- **Scenario**:
    1. Define two distinct domains `D1` and `D2`.
    2. Assign security levels `L(D1)` and `L(D2)`.
    3. Assume `LatticeLeq(L(D1), L(D2))` is true.
    4. Assume `LatticeLeq(L(D2), L(D1))` is true.
- **Expected Outcome**: For both conditions to be true, it must necessarily be that `L(D1).cls = L(D2).cls` and `L(D1).cats = L(D2).cats`.
- **Falsification Condition**: If it's possible for `LatticeLeq(L(D1), L(D2))` and `LatticeLeq(L(D2), L(D1))` to both be true, yet `L(D1).cls ≠ L(D2).cls` or `L(D1).cats ≠ L(D2).cats`. This would imply the `≤` relation does not correctly enforce antisymmetry for distinct security levels.

### Test DL.3: Transitivity (`d1 ≤ d2` AND `d2 ≤ d3` => `d1 ≤ d3`)
- **Property**: `∀ d1, d2, d3 ∈ Domains: (L(d1) ≤ L(d2) AND L(d2) ≤ L(d3)) ⇒ L(d1) ≤ L(d3)`.
- **Scenario**:
    1. Define three domains `D1`, `D2`, `D3`.
    2. Assign security levels such that `L(D1) ≤ L(D2)` and `L(D2) ≤ L(D3)`. For example:
        - `L(D1) = (1, {"A"})`
        - `L(D2) = (2, {"A", "B"})` (so `L(D1) ≤ L(D2)`)
        - `L(D3) = (3, {"A", "B", "C"})` (so `L(D2) ≤ L(D3)`)
    3. Evaluate `LatticeLeq(L(D1), L(D3))`.
- **Expected Outcome**: The evaluation `LatticeLeq(L(D1), L(D3))` must return `True`.
- **Falsification Condition**: The evaluation returns `False`. This would indicate a failure in the transitivity property of the defined `≤` relation.

### Test DL.4: LUB/GLB Operation Correctness
- **Property**: The Join (`⊔`) and Meet (`⊓`) operations correctly compute the Least Upper Bound (LUB) and Greatest Lower Bound (GLB) of security levels.
- **Scenario (LUB - Join)**:
    1. `L(D1) = (cls1, cats1) = (1, {"NET"})`
    2. `L(D2) = (cls2, cats2) = (2, {"FS"})`
    3. Compute `L_join = L(D1) ⊔ L(D2)`.
- **Expected Outcome (LUB - Join)**: `L_join = (max(1,2), {"NET"} ∪ {"FS"}) = (2, {"NET", "FS"})`.
- **Scenario (GLB - Meet)**:
    1. `L(D1) = (cls1, cats1) = (2, {"NET", "FS"})`
    2. `L(D2) = (cls2, cats2) = (1, {"FS", "IPC"})`
    3. Compute `L_glb = L(D1) ⊓ L(D2)`.
- **Expected Outcome (GLB - Meet)**: `L_glb = (min(2,1), {"NET", "FS"} ∩ {"FS", "IPC"}) = (1, {"FS"})`.
- **Falsification Condition**: If the computed `L_join` or `L_glb` does not match the expected outcome based on the formal definitions (`max/min` for classifications, `union/intersection` for categories).

### Test DL.5: Completeness (Top ⊤ and Bottom ⊥ Elements)
- **Property**: The System Domain `D_K` is the top element (⊤) and the Null Domain `D_∅` is the bottom element (⊥) of the lattice.
    - `L(D_K) = (max_cls, AllCats)`
    - `L(D_∅) = (min_cls, ∅)`
- **Scenario**:
    1. For an arbitrary domain `D_p` with `L(D_p)`, evaluate `LatticeLeq(L(D_p), L(D_K))`.
    2. For an arbitrary domain `D_p` with `L(D_p)`, evaluate `LatticeLeq(L(D_∅), L(D_p))`.
- **Expected Outcome**: Both evaluations must return `True` for any `D_p`.
- **Falsification Condition**: If `LatticeLeq(L(D_p), L(D_K))` returns `False` for any `D_p`, or if `LatticeLeq(L(D_∅), L(D_p))` returns `False` for any `D_p`.

## 3. Delegation Algebra Specification Test Cases

Let `δ(c_parent, d_target, r_mask)` be the delegation operation.
`d_source` is the owner of `c_parent`.

### Test DA.1: Delegation Permission Policy (Cannot Delegate Upwards)
- **Property**: Delegation `δ(c_parent, d_target, r_mask)` is permitted only if `L(d_target) ≤ L(d_source)`.
- **Scenario**:
    1. Define domain `D_S` (source) with `L(D_S) = (User_Standard, {"APP"})`.
    2. Define domain `D_T` (target) with `L(D_T) = (Supervisor, {"APP"})`. Note: `L(D_T) <binary data, 1 bytes><binary data, 1 bytes> L(D_S)`.
    3. `D_S` owns a capability `c_S` with `DELEGATE_RIGHT`.
    4. Attempt to perform `δ(c_S, D_T, some_rights_mask)`.
- **Expected Outcome**: The delegation operation should be disallowed due to failing the pre-condition `L(D_T) ≤ L(D_S)`. No new capability should be created for `D_T`.
- **Falsification Condition**: If the delegation operation succeeds and `c_T` is created for `D_T`.

### Test DA.2: Rights Attenuation
- **Property**: `rights(c_child) = rights(c_parent) ∩ r_mask`, ensuring `rights(c_child) ⊆ rights(c_parent)`.
- **Scenario**:
    1. `d_source` owns `c_parent` with `rights(c_parent) = {READ, WRITE, DELEGATE_RIGHT}`.
    2. `d_source` attempts to delegate `c_parent` to `d_target` (assume `L(d_target) ≤ L(d_source)` holds) with `r_mask = {READ, EXECUTE_RIGHT}`.
    3. Let `c_child` be the resulting capability.
- **Expected Outcome**: `rights(c_child)` must be `{READ, WRITE, DELEGATE_RIGHT} ∩ {READ, EXECUTE_RIGHT} = {READ}`.
- **Falsification Condition**: If `rights(c_child)` is anything other than `{READ}`. For example, if it includes `WRITE`, `DELEGATE_RIGHT`, or `EXECUTE_RIGHT`.

### Test DA.3: Missing DELEGATE_RIGHT Prevents Delegation
- **Property**: The `rights(c_parent)` must include `DELEGATE_RIGHT` for delegation to be permitted.
- **Scenario**:
    1. `d_source` owns `c_parent` with `rights(c_parent) = {READ, WRITE}` (no `DELEGATE_RIGHT`).
    2. `d_source` attempts to delegate `c_parent` to `d_target` (assume `L(d_target) ≤ L(d_source)` holds).
- **Expected Outcome**: The delegation operation should fail its pre-condition check for `DELEGATE_RIGHT`. No new capability should be created.
- **Falsification Condition**: If the delegation operation succeeds and `c_child` is created.

## 4. Vector Timestamp Protocol Test Cases

Let `V_i` be the vector timestamp of domain `D_i`. `V_i[k]` is `D_i`'s knowledge of `D_k`'s clock. `V_i[i]` is `D_i`'s local clock.
`V(event_x)` is the VT associated with event `x`.

### Test VT.1: Local Event Increment
- **Property**: A local event at domain `D_i` increments only `V_i[i]`.
- **Scenario**:
    1. Domain `D1` has `V1_before = (c1, c2, c3, ..., cN)`.
    2. `D1` performs a significant local event.
- **Expected Outcome**: `V1_after = (c1+1, c2, c3, ..., cN)`.
- **Falsification Condition**: If `V1_after[1] ≠ c1+1`, or if any `V1_after[k] ≠ ck` for `k ≠ 1`.

### Test VT.2: Update on Send
- **Property**: When `D_i` sends a message, it first increments `V_i[i]`, and this updated `V_i` is attached to the message.
- **Scenario**:
    1. Domain `D1` has `V1_current = (c1, c2, ..., cN)`.
    2. `D1` prepares to send a message.
- **Expected Outcome**:
    1. `D1` updates `V1_current[1] := V1_current[1] + 1`. Let this be `V1_updated`.
    2. The message carries `V_msg = V1_updated`.
- **Falsification Condition**: If the message carries a VT where the sender's own clock component was not incremented immediately prior to sending, or if it's an older VT.

### Test VT.3: Update on Receive
- **Property**: When `D_j` receives a message with `V_msg` from `D_i`:
    1. `∀k: V_j_intermediate[k] = max(V_j_old[k], V_msg[k])`.
    2. `V_j_new[j] = V_j_intermediate[j] + 1`, and `V_j_new[k] = V_j_intermediate[k]` for `k ≠ j`.
- **Scenario**:
    1. `D2` has `V2_old = (1, 1, 0)`.
    2. `D2` receives a message from `D1` with `V_msg = (2, 0, 0)`.
- **Expected Outcome**:
    1. Intermediate merge: `V_merged = (max(1,2), max(1,0), max(0,0)) = (2,1,0)`.
    2. Final `V2_new` after local increment for receive event: `(2, 1+1, 0) = (2,2,0)`.
- **Falsification Condition**: If `V2_new` is not `(2,2,0)`.

### Test VT.4: Happened-Before (`a → b` => `V(a) < V(b)`)
- **Property**: If event `a` happened before event `b`, then the vector timestamp of `a` must be strictly less than the vector timestamp of `b`.
- **Scenario**:
    1. Event `a`: `D1` performs a local action. `V(a) = V1_after_action = (c1, c2, ..., cN)`.
    2. `D1` sends a message `m` to `D2`. The VT on `m` is `V_msg = VTSend(V(a), D1_idx)`. (So `V_msg[D1_idx] = c1+1`).
    3. Event `b`: `D2` receives message `m`. `V(b) = VTReceive(V2_before_recv, V_msg, D2_idx)`.
- **Expected Outcome**: The comparison `V(a) < V(b)` must be true.
    Example: `V(a) = (1,0,0)`. `D1` sends to `D2`. `V_msg = (2,0,0)`.
    `D2` (initially `(0,0,0)`) receives. `V(b) = (max(0,2), max(0,0), max(0,0))` then local inc `(2,0,0)` -> `(2,1,0)`.
    So, `(1,0,0) < (2,1,0)` is true.
- **Falsification Condition**: If the comparison `V(a) < V(b)` is false according to the VT comparison rules (i.e., `V(a)` is not strictly less than `V(b)`).

### Test VT.5: Concurrency (`a || b` => `¬(V(a) < V(b))` AND `¬(V(b) < V(a))`)
- **Property**: If events `a` and `b` are concurrent, their vector timestamps must be incomparable.
- **Scenario**:
    1. Event `a`: `D1` performs a local action. `V(a) = (1,0,0)` (assuming 3 domains).
    2. Event `b`: `D2` performs a local action, with no communication with `D1` before this event. `V(b) = (0,1,0)`.
- **Expected Outcome**: `V(a)` and `V(b)` are incomparable: `¬(V(a) < V(b))` is true, AND `¬(V(b) < V(a))` is true.
- **Falsification Condition**: If `V(a) < V(b)` is true, or if `V(b) < V(a)` is true.

## 5. Cross-Specification Test Cases (Conceptual)

These tests examine interactions between the different formal models.

### Test CS.1: Epoch Update Propagation, Causality, and Capability Use
- **Property**: A capability delegated or used reflects the causal state (epoch and other relevant VT-ordered events) of the domains involved in its lifecycle up to that point.
- **Scenario**:
    1. `D_Grandparent` (DG) has epoch `E_G1`, `V_DG = (g,_,_)`. DG advances epoch to `E_G2` (event `ev_G_epoch`). `V_DG` becomes `(g+1,_,_)`.
    2. `D_Parent` (DP) (initially `V_DP=(g,p,_)`, knowing `E_G1`) receives epoch update from DG (event `ev_P_recv_G`). `V_DP` updates based on DG's VT, `V_DP[P]` increments. DP updates its epoch to `E_P1` based on `E_G2`.
    3. `D_Parent` delegates a capability `C_P` (reflecting epoch `E_P1`) to `D_Child` (DC) (event `ev_P_send_cap`). `V_DP[P]` increments. Message to DC contains `C_P` and `V_DP`.
    4. `D_Child` (initially `V_DC=(g,p,c)`) receives `C_P` (event `ev_C_recv_cap`). `V_DC` updates based on `V_DP`, `V_DC[C]` increments.
    5. Concurrently or later, `D_Grandparent` might attempt to revoke capabilities related to epoch `E_G1` or `E_G2`.
- **Expected Outcome**:
    - Vector timestamps must ensure `ev_G_epoch → ev_P_recv_G → ev_P_send_cap → ev_C_recv_cap`.
    - `V_DC` after receiving `C_P` must reflect a value for `V_DC[DG_idx]` that is at least `g+1`.
    - `C_P` as held by `D_Child` should be associated (implicitly or explicitly) with an epoch state (`E_P1`) that is causally consistent with `E_G2`.
    - If `D_Grandparent` revokes based on `E_G1`, `C_P` (derived under rules based on `E_G2`) should remain valid. If revocation targets `E_G2`, `C_P` might become invalid. The VTs help ensure that operations at `D_Child` using `C_P` are correctly ordered with respect to these potential revocations.
- **Falsification Condition**:
    - If `V_DC[DG_idx]` after `ev_C_recv_cap` is less than `g+1`, indicating a loss of causal information about DG's epoch update.
    - If `D_Child` can use `C_P` in a way that violates epoch rules, e.g., if `C_P`'s validity is tied to an epoch `E_P_old < E_P1` due to misordered updates at `D_Parent` or `D_Child` not captured by VTs.
    - If a revocation by `D_Grandparent` based on `E_G2` is not correctly applied to `C_P` at `D_Child` because `D_Child`'s VT state does not properly reflect its causal dependency on `E_G2` via `D_Parent`.

This list is not exhaustive but provides a conceptual starting point for designing tests that can rigorously challenge the assumptions and properties of FeuerBird's formal security models.
