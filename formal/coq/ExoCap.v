(* ExoCap - Exokernel Capability Verification *)
(* Rocq Prover 9.x compatible *)

From Stdlib Require Import NArith.
From Stdlib Require Import Arith.

Open Scope N_scope.

Record exo_cap := { cid : nat; rights : N; owner : nat; tag : N }.

Definition compute_tag (id : nat) (rights : N) (owner : nat) : N :=
  (N.of_nat id + rights + N.of_nat owner)%N.

Definition cap_new (id : nat) (rights : N) (owner : nat) : exo_cap :=
  {| cid := id; rights := rights; owner := owner;
     tag := compute_tag id rights owner |}.

Definition cap_verify (c : exo_cap) : bool :=
  N.eqb (compute_tag (cid c) (rights c) (owner c)) (tag c).

Definition cap_has_rights (r need : N) : bool :=
  N.eqb (N.land r need) need.

Lemma cap_new_verify : forall id r o,
  cap_verify (cap_new id r o) = true.
Proof.
  intros; unfold cap_verify, cap_new, compute_tag; simpl.
  now rewrite N.eqb_refl.
Qed.
