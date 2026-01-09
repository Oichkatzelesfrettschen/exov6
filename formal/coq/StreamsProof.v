(* StreamsProof - STREAMS Protocol Buffer Verification *)
(* Rocq Prover 9.x compatible *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Nat.
From Stdlib Require Import Lia.
Import ListNotations.

Definition STREAM_BUFSZ := 32%nat.

Record stream_state := {
  sbuf : nat -> nat;
  sr : nat;
  sw : nat;
  locked : bool
}.

Definition stream_inv (s : stream_state) : Prop :=
  sr s <= sw s /\
  sw s - sr s <= STREAM_BUFSZ /\
  exists pending,
    length pending = sw s - sr s /\
    forall i, i < length pending ->
      sbuf s ((sr s + i) mod STREAM_BUFSZ) = nth i pending 0.

Definition yield (s : stream_state) : stream_state :=
  {| sbuf := sbuf s; sr := S (sr s); sw := sw s; locked := locked s |}.

Definition stop (s : stream_state) : stream_state :=
  {| sbuf := sbuf s; sr := sr s; sw := sw s; locked := false |}.

Lemma yield_preserves : forall s,
  stream_inv s -> sr s < sw s -> stream_inv (yield s).
Proof.
  intros s [Hle [Hbound [pending [Hlen Hbuf]]]] Hlt.
  unfold yield, stream_inv.
  split; [simpl; lia|].
  split; [simpl; lia|].
  exists (skipn 1 pending).
  assert (Hge1: length pending >= 1) by (rewrite Hlen; lia).
  split.
  - rewrite length_skipn. rewrite Hlen. simpl. lia.
  - intros i Hi. cbn [sr sbuf].
    rewrite length_skipn in Hi.
    specialize (Hbuf (S i)).
    assert (Hsi: S i < length pending) by lia.
    specialize (Hbuf Hsi).
    rewrite nth_skipn.
    replace (S (sr s) + i) with (sr s + S i) by lia.
    exact Hbuf.
Qed.

Lemma stop_releases : forall s,
  locked s = true -> locked (stop s) = false.
Proof.
  intros s Hlocked. unfold stop. simpl. reflexivity.
Qed.
