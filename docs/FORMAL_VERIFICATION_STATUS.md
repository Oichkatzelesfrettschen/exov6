# FeuerBird Exokernel - Formal Verification Status

**Date:** 2026-01-08
**Rocq Version:** 9.1.0 (Rocq Prover, formerly Coq)
**Status:** All proofs compile successfully

---

## Overview

The FeuerBird Exokernel includes mechanized formal verification using the Rocq Prover (formerly Coq). These proofs verify critical invariants for kernel subsystems including capability management, IRQ handling, and stream processing.

## Verified Components

### 1. ExoCap.v - Exokernel Capability Authentication

**Location:** `formal/coq/ExoCap.v`
**Size:** 30 lines
**Compiled Object:** 4.9KB

Verifies the capability authentication mechanism:

- `exo_cap` record with `cid`, `rights`, `owner`, and `tag` fields
- `compute_tag` function for tag generation
- `cap_new` constructor and `cap_verify` predicate
- `cap_has_rights` permission checking

**Key Theorem:**
```coq
Lemma cap_new_verify : forall id r o,
  cap_verify (cap_new id r o) = true.
```

Guarantees that freshly created capabilities always pass verification.

### 2. LambdaCap.v - Linear Capability Semantics

**Location:** `formal/coq/LambdaCap.v`
**Size:** 90 lines
**Compiled Object:** 9.0KB

Verifies linear (single-use) capability semantics:

- `lambda_cap` record with `consumed` state
- `lambda_cap_use`, `lambda_cap_delegate`, `lambda_cap_revoke` operations
- Single-use enforcement

**Key Theorems:**
```coq
Theorem use_once : forall lc lc1 r1 lc2 r2,
  lambda_cap_use lc = (lc1, r1) ->
  r1 = true ->
  lambda_cap_use lc1 = (lc2, r2) ->
  r2 = false.

Theorem delegate_preserves_single_use : forall lc lc1 r1 lc2 r2 lc3 r3,
  consumed lc = false ->
  lambda_cap_delegate lc = (lc1, r1) ->
  r1 = true ->
  lambda_cap_use lc1 = (lc2, r2) ->
  r2 = true ->
  lambda_cap_use lc2 = (lc3, r3) ->
  r3 = false.
```

Guarantees that capabilities can only be used once, even after delegation.

### 3. IRQProof.v - IRQ Queue Ring Buffer Invariants

**Location:** `formal/coq/IRQProof.v`
**Size:** 149 lines
**Compiled Object:** 102KB

Verifies the IRQ queue ring buffer implementation:

- `irq_queue` record with `buf`, `r` (read), `w` (write) indices
- Buffer size constant `IRQ_BUFSZ = 32`
- Queue invariant maintaining read/write ordering and pending element tracking

**Key Theorems:**
```coq
Lemma irq_wait_preserves : forall q,
  queue_inv q -> r q < w q -> queue_inv (irq_wait q).

Lemma irq_trigger_preserves : forall q irq,
  queue_inv q -> w q - r q < IRQ_BUFSZ -> queue_inv (irq_trigger irq q).
```

Guarantees that reading (wait) and writing (trigger) operations preserve the queue invariant.

### 4. StreamsProof.v - STREAMS Protocol Buffer Verification

**Location:** `formal/coq/StreamsProof.v`
**Size:** 65 lines
**Compiled Object:** 21KB

Verifies STREAMS protocol buffer operations:

- `stream_state` record with `sbuf`, `sr`, `sw`, and `locked` fields
- `yield` and `stop` operations
- Stream invariant similar to IRQ queue

**Key Theorems:**
```coq
Lemma yield_preserves : forall s,
  stream_inv s -> sr s < sw s -> stream_inv (yield s).

Lemma stop_releases : forall s,
  locked s = true -> locked (stop s) = false.
```

---

## Rocq 9.x Compatibility Notes

The proofs were updated for Rocq 9.x compatibility:

1. **Import Changes:** All imports changed from `Require Import Coq.*` to `From Stdlib Require Import`
2. **Deprecated Lemmas:**
   - `skipn_length` -> `length_skipn`
   - `app_length` -> `length_app`
   - `Nat.add_mod` -> `Div0.add_mod` (warnings only, still functional)
   - `Nat.mod_eq` -> `Div0.mod_eq` (warnings only, still functional)

---

## Build Instructions

```bash
cd formal/coq

# Compile all proofs
for f in ExoCap.v LambdaCap.v StreamsProof.v IRQProof.v; do
  coqc -Q . FeuerBird "$f"
done

# Or use the CMake integration
ninja -C build coq-check
```

---

## Relationship to Implementation

| Proof File | C Implementation | Kernel Subsystem |
|------------|------------------|------------------|
| ExoCap.v | `kernel/cap.c`, `kernel/exo_cap.h` | Capability tables |
| LambdaCap.v | `kernel/lambda_cap.c` | Linear capabilities |
| IRQProof.v | `kernel/irq.c` | IRQ handling |
| StreamsProof.v | `kernel/ipc/streams.c` | STREAMS IPC |

---

## TLA+ Specifications

In addition to Coq proofs, the project includes TLA+ specifications:

- `formal/tla/Capability.tla` - Capability lifecycle model
- `formal/tla/ExoCap.tla` - Exokernel capability model
- `formal/tla/StreamsLocks.tla` - STREAMS locking protocol

These provide complementary model checking verification.

---

## Future Work

1. **Expand IRQ verification:** Add interrupt priority and nested IRQ handling
2. **Memory allocator proofs:** Verify page allocator invariants
3. **IPC ordering guarantees:** Prove message ordering properties
4. **Scheduler fairness:** Verify CFS-style timeline scheduler properties
5. **CI Integration:** Add Coq compilation to GitHub Actions

---

*Generated: 2026-01-08*
*Rocq Prover: 9.1.0*
