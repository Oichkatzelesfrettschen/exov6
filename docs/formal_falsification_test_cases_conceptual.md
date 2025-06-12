# Falsification Test Cases (Conceptual) for FeuerBird Formal Specifications

## 1. Introduction

### Purpose
This document outlines conceptual test cases designed to falsify—that is, to find violations or contradictions in—the formal specifications developed for FeuerBird. These specifications include the Domain Security Lattice, the Capability Delegation Algebra, the Vector Timestamp Protocol, and by extension, the core invariants of the associated TLA+ model.

### Approach
The test cases describe scenarios, conditions, or states that, if observed or achievable within a formal model (like a TLA+ specification checked by TLC) or a concrete implementation, would indicate a flaw or a contradiction to the defined properties, theorems, or invariants. These conceptual tests serve multiple purposes:
- Guide the development and refinement of formal models by highlighting edge cases and critical properties to verify.
- Assist in formulating specific assertions, invariants, and temporal properties to be checked by model checkers like TLC.
- Provide a basis for developing concrete unit and integration tests for the eventual C23 implementation of these mechanisms.
- Serve as pedagogical tools to help understand the implications and guarantees of each formal specification.

The focus is on identifying conditions that *should not* occur if the specifications are correctly defined and implemented.

## 2. Test Cases for Domain Lattice Specification

Let `dl` represent an instance of the Domain Lattice. `LatticeLeq(dl, d1, d2)` checks if `d1 ≤ d2`.

- **Reflexivity (`d ≤ d`)**:
    - *Test DL-R-1*:
        - Scenario: Define an arbitrary domain `d` with security level `L(d)`.
        - Check: Does `LatticeLeq(dl, d, d)` evaluate to True?
        - Expected Outcome: True.
        - Falsified if: `LatticeLeq(dl, d, d)` is False.

- **Antisymmetry (`d1 ≤ d2 AND d2 ≤ d1 ⇒ d1 = d2`)**:
    - *Test DL-AS-1*:
        - Scenario: Define two distinct domains `d1` and `d2` (i.e., `L(d1) ≠ L(d2)`).
        - Check: If `LatticeLeq(dl, d1, d2)` is True AND `LatticeLeq(dl, d2, d1)` is True.
        - Expected Outcome: This combined condition should be False if `d1 ≠ d2`.
        - Falsified if: Both `LatticeLeq(dl, d1, d2)` and `LatticeLeq(dl, d2, d1)` hold true for `d1` and `d2` that are demonstrably different (e.g., different classifications or category sets).

- **Transitivity (`d1 ≤ d2 AND d2 ≤ d3 ⇒ d1 ≤ d3`)**:
    - *Test DL-T-1*:
        - Scenario: Define three domains `d1, d2, d3`. Establish that `LatticeLeq(dl, d1, d2)` is True AND `LatticeLeq(dl, d2, d3)` is True.
        - Check: Does `LatticeLeq(dl, d1, d3)` evaluate to True?
        - Expected Outcome: True.
        - Falsified if: `LatticeLeq(dl, d1, d3)` is False under these conditions.

- **Join Operation Correctness (`d_join = d1 ⊔ d2`)**:
    - *Test DL-J-1*:
        - Scenario: Define domains `d1, d2`. Compute `d_join` using the specified Join operation (max of classifications, union of categories).
        - Check 1: Is `LatticeLeq(dl, d1, d_join)` True?
        - Check 2: Is `LatticeLeq(dl, d2, d_join)` True?
        - Check 3: For any arbitrary domain `dx` such that `LatticeLeq(dl, d1, dx)` is True AND `LatticeLeq(dl, d2, dx)` is True, does `LatticeLeq(dl, d_join, dx)` also hold True? (This verifies `d_join` is the *Least* Upper Bound).
        - Expected Outcome: All checks (1, 2, 3) must be True.
        - Falsified if: Any of these checks fail.

- **Meet Operation Correctness (`d_meet = d1 ⊓ d2`)**:
    - *Test DL-M-1*:
        - Scenario: Define domains `d1, d2`. Compute `d_meet` using the specified Meet operation (min of classifications, intersection of categories).
        - Check 1: Is `LatticeLeq(dl, d_meet, d1)` True?
        - Check 2: Is `LatticeLeq(dl, d_meet, d2)` True?
        - Check 3: For any arbitrary domain `dx` such that `LatticeLeq(dl, dx, d1)` is True AND `LatticeLeq(dl, dx, d2)` is True, does `LatticeLeq(dl, dx, d_meet)` also hold True? (This verifies `d_meet` is the *Greatest* Lower Bound).
        - Expected Outcome: All checks (1, 2, 3) must be True.
        - Falsified if: Any of these checks fail.

- **Top/Bottom Elements (`RootDomain` as ⊤, `NullDomain` as ⊥)**:
    - *Test DL-TB-1 (Top Element)*:
        - Scenario: For every domain `d` in the set of all defined domains `D`.
        - Check: Is `LatticeLeq(dl, d, RootDomain)` True?
        - Expected Outcome: True for all `d`.
        - Falsified if: False for any `d`.
    - *Test DL-TB-2 (Bottom Element)*:
        - Scenario: For every domain `d` in `D`.
        - Check: Is `LatticeLeq(dl, NullDomain, d)` True?
        - Expected Outcome: True for all `d`.
        - Falsified if: False for any `d`.

## 3. Test Cases for Delegation Algebra Specification

- **Pre-condition: `DELEGATE` Right**:
    - *Test DA-P1*:
        - Scenario: Domain `d_source` owns capability `c_parent`. The `rights` field of `c_parent` does NOT contain `DELEGATE_RIGHT`. `d_source` attempts to delegate `c_parent` to `d_target`.
        - Check: Is the delegation operation `δ(c_parent, d_target, r_mask)` permitted/successful?
        - Expected Outcome: Delegation operation should fail or be disallowed.
        - Falsified if: The delegation proceeds and `c_child` is created.

- **Pre-condition: Lattice Order (`L(d_target) ≤ L(d_source)`)**:
    - *Test DA-P2*:
        - Scenario: Domain `d_source` (owner of `c_parent` with `DELEGATE_RIGHT`) attempts to delegate `c_parent` to `d_target`. The security levels are such that `L(d_target) ≤ L(d_source)` is False (i.e., `d_target` is strictly more privileged or in an incomparable higher part of the lattice).
        - Check: Is the delegation operation `δ(c_parent, d_target, r_mask)` permitted/successful?
        - Expected Outcome: Delegation operation should fail or be disallowed.
        - Falsified if: The delegation proceeds and `c_child` is created.

- **Property: Rights Attenuation (`rights(c_child) ⊆ rights(c_parent)`)**:
    - *Test DA-R1*:
        - Scenario: A valid delegation occurs: `c_child = δ(c_parent, d_target, r_mask)`.
        - Check: Are the rights of `c_child` exactly `rights(c_parent) ∩ r_mask`? Specifically, check if any right bit is set in `rights(c_child)` that is not also set in `(rights(c_parent) ∩ r_mask)`.
        - Expected Outcome: `rights(c_child) = (rights(c_parent) ∩ r_mask)` must hold. Thus, `rights(c_child) ⊆ rights(c_parent)` must also hold.
        - Falsified if: `rights(c_child)` contains any right not present in `rights(c_parent)`, or any right not present in `r_mask` (unless that right was also not in `rights(c_parent)`). The key is no amplification beyond `rights(c_parent)` and no rights granted beyond `r_mask`.

- **Property: Type/Resource Preservation**:
    - *Test DA-TR1*:
        - Scenario: A valid delegation occurs: `c_child = δ(c_parent, d_target, r_mask)`.
        - Check 1: Is `type(c_child) == type(c_parent)`?
        - Check 2: Is `resource(c_child) == resource(c_parent)`?
        - Expected Outcome: Both checks must be True.
        - Falsified if: Either `type` or `resource` differs between `c_parent` and `c_child`.

## 4. Test Cases for Vector Timestamp Protocol Specification

Let `V_i_old` be the VT of domain `d_i` before an event, and `V_i_new` after.

- **Local Event Rule**:
    - *Test VT-LE1*:
        - Scenario: Domain `d_i` performs a significant local event (not a send/receive).
        - Check: Is `V_i_new[i] == V_i_old[i] + 1`?
        - Check: For all `k ≠ i`, is `V_i_new[k] == V_i_old[k]`?
        - Expected Outcome: Both true.
        - Falsified if: `V_i[i]` does not increment, or any other component `V_i[k]` changes.

- **Send Rule**:
    - *Test VT-S1*:
        - Scenario: Domain `d_i` sends a message `m`. Let `V_i_before_send` be its VT before the send operation's local clock increment. Let `V_msg` be the timestamp attached to `m`.
        - Check 1: Is `V_i_after_send_increment[i] == V_i_before_send[i] + 1`?
        - Check 2: Is `V_msg` identical to `V_i_after_send_increment`?
        - Expected Outcome: Both true.
        - Falsified if: `V_i[i]` does not increment before sending, or `V_msg` does not reflect this incremented VT.

- **Receive Rule**:
    - *Test VT-R1*:
        - Scenario: Domain `d_j` (with current VT `V_j_old`) receives message `m` from `d_i` with timestamp `V_msg`. Let `V_j_new` be `d_j`'s VT after processing the receipt.
        - Check 1 (Merge): For every component `k`, is `V_j_temp[k] == max(V_j_old[k], V_msg[k])` where `V_j_temp` is the state after merging but before local increment?
        - Check 2 (Local Increment): Is `V_j_new[j] == V_j_temp[j] + 1`?
        - Check 3 (Other Components): For every `k ≠ j`, is `V_j_new[k] == V_j_temp[k]`?
        - Expected Outcome: All true.
        - Falsified if: The merge rule is incorrect, or the local clock `V_j[j]` does not increment post-merge, or other components change during the local increment.

- **Happened-Before (`a → b ⇔ V(a) < V(b)`)**:
    - *Test VT-HB1 (Causality via Message)*:
        - Scenario: Event `a` is the sending of message `m` by `d_i` (timestamp `V(a)` is `V_i` after increment, sent as `V_msg`). Event `b` is the receipt of `m` by `d_j` (timestamp `V(b)` is `V_j` after merge and increment).
        - Check: Is `V(a) < V(b)`? (Specifically, `V_msg < V(b)` should hold).
        - Expected Outcome: True.
        - Falsified if: `V(a) < V(b)` is False. (This would mean `V_msg[i] > V(b)[i]` for some `i` or they are concurrent, which is impossible if rules are followed).
    - *Test VT-HB2 (Concurrency)*:
        - Scenario: Event `a` occurs in `d_i` (resulting in `V(a)`). Event `c` occurs in `d_k` (resulting in `V(c)`). No messages are exchanged between `d_i` and `d_k` (or indirectly through other domains) that could establish a causal link between `a` and `c`.
        - Check: Is `¬(V(a) < V(c))` AND `¬(V(c) < V(a))`?
        - Expected Outcome: True (events are concurrent).
        - Falsified if: A happened-before relationship (`<`) is established in either direction.

## 5. Test Cases for TLA+ Model Core Invariants

These tests describe scenarios that, if allowed by the TLA+ model, would violate its specified invariants. `Foo'` denotes the value of `Foo` in the next state.

- **`InvariantEpochMonotonicity(domain)`**: `domainEpochs'[domain] ≥ domainEpochs[domain]`
    - *Test TLA-EM1*:
        - Scenario: Let `domainEpochs[d1] = 5`. An action occurs (e.g., `UpdateEpoch(d1, 4)` or a faulty `LearnOtherDomainState` where a stale, smaller epoch is adopted).
        - Check: Does the model allow a transition to a state where `domainEpochs'[d1] = 4`?
        - Expected Outcome for invariant preservation: Such a transition should be disallowed by the model's action guards or definitions if the invariant is to hold.
        - Falsified if: The model permits `domainEpochs'[d1] < domainEpochs[d1]`.

- **`InvariantDelegationRightsMonotonicity(parentCap, childCap)`**: `childCap.rights ⊆ parentCap.rights`
    - *Test TLA-DRM1*:
        - Scenario: `parentCap` exists with `parentCap.rights = {"READ"}`. The action `DelegateCapability(parentCap, targetDom, ownerDom, {"READ", "WRITE"})` is attempted (where `r_mask` is `{"READ", "WRITE"}`).
        - Check: If this action results in `childCap` where `childCap.rights = {"READ", "WRITE"}`.
        - Expected Outcome for invariant preservation: The effective rights of `childCap` should be `parentCap.rights ∩ {"READ", "WRITE"}`, which is `{"READ"}`.
        - Falsified if: The model allows `childCap.rights` to contain "WRITE".

- **`InvariantDelegationLatticeOrder(delegatorDom, targetDom)`**: `ENABLED DelegateCapability(...) ⇒ LatticeLeq(TargetDomainSecurityLevel(targetDom), DomainSecurityLevel(delegatorDom))`
    - *Test TLA-DLO1*:
        - Scenario: Set up domains `delegatorDom` and `targetDom` such that `LatticeLeq(TargetDomainSecurityLevel(targetDom), DomainSecurityLevel(delegatorDom))` is False (e.g., `targetDom` is more privileged).
        - Check: Is the `DelegateCapability` action (from `delegatorDom` to `targetDom`) enabled in the TLA+ model?
        - Expected Outcome for invariant preservation: The `DelegateCapability` action should NOT be enabled.
        - Falsified if: The action is enabled under these conditions.

- **`InvariantVectorTimestampMonotonicity(domain, idx)`**: `vectorTimestamps'[domain][idx] ≥ vectorTimestamps[domain][idx]` (especially `vectorTimestamps'[domain][IndexOf(domain)] ≥ vectorTimestamps[domain][IndexOf(domain)]`, and local clock only increases by 1 for its own events or stays same if other components update due to merge).
    - *Test TLA-VTM1*:
        - Scenario: Let `vectorTimestamps[d1][IndexOf(d1)] = 5`. An action occurs that is not a local event for `d1` nor a message receive event at `d1`.
        - Check: Does the model allow `vectorTimestamps'[d1][IndexOf(d1)]` to become anything other than 5? Or if it was a local event, anything other than 6? Or if it was a receive, anything less than what `max` dictates?
        - Expected Outcome for invariant preservation: `vectorTimestamps[d1][idx]` should not decrease. `vectorTimestamps[d1][IndexOf(d1)]` should only increment by 1 for its own local/send/receive events or stay the same if only merging external changes.
        - Falsified if: Any component of a VT illicitly decreases, or `VT[d][d]` changes when it shouldn't or increments by more than 1 without justification.

- **`InvariantVectorTimestampCausality(learnerDom, sourceDom, msgVT)`**: (Related to `ReceiveMessage` action)
  `vectorTimestamps'[learnerDom][IndexOf(learnerDom)] = vectorTimestamps[learnerDom][IndexOf(learnerDom)] + 1` AND
  `∀k ∈ DOMAINS: vectorTimestamps'[learnerDom][k] = MAX(vectorTimestamps[learnerDom][k], msgVT[k])` (before local increment on `learnerDom`'s own index).
    - *Test TLA-VTC1*:
        - Scenario: `learnerDom` (with `VT_learner_old`) receives a message from `sourceDom` carrying `VT_msg`.
        - Check 1: After the merge step, are all components `vectorTimestamps_merged[learnerDom][k] == MAX(VT_learner_old[k], VT_msg[k])`?
        - Check 2: Is `vectorTimestamps_final[learnerDom][IndexOf(learnerDom)] == vectorTimestamps_merged[learnerDom][IndexOf(learnerDom)] + 1`?
        - Expected Outcome for invariant preservation: Both true.
        - Falsified if: The merge rule is not correctly applied, or the local component of `learnerDom`'s VT is not incremented after the merge.

## 6. Pedagogical Integration Notes

- **Manual Tracing**: For each formal specification (Domain Lattice, Delegation Algebra, Vector Timestamps), a small, illustrative subset of these falsification test cases can be selected. Students or developers can manually trace these scenarios against the specification's rules to gain a deeper understanding of the properties being enforced or protected.
- **TLA+ Model Checking**: When using TLC (TLA+ Model Checker), these conceptual tests directly inform the formulation of:
    - **Invariants**: Many of these tests are direct checks against defined invariants (e.g., `InvariantEpochMonotonicity`).
    - **State Constraints or Properties**: Some tests can be translated into temporal properties or state assertions that TLC can check (e.g., ensuring that if a delegation occurs, the rights attenuation property holds for the resulting capability).
    - **Deadlock Checks**: While not explicitly falsification tests for properties, checking for deadlock (`CHECK deadlock FALSE`) is crucial and can reveal issues in action definitions that might relate to pre-conditions not being met as expected.
- **Implementation Testing**: These conceptual scenarios form the basis for creating unit tests, integration tests, and system-level tests for the C23 implementation, ensuring it adheres to the formal specifications.

This document serves as a foundational guide for rigorous verification and validation of FeuerBird's core security mechanisms, bridging the gap between formal specification and practical testing.
