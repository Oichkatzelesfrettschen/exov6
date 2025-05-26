Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
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
  unfold yield.
  repeat split.
  - lia.
  - lia.
  - exists (skipn 1 pending).
    assert (Hlen': length pending = sw s - sr s) by auto.
    assert (length pending >= 1) by (rewrite Hlen; lia).
    rewrite skipn_length; [|lia].
    split.
    + rewrite Hlen. simpl. lia.
    + intros i Hi.
      specialize (Hbuf (S i)).
      assert (Hsi: S i < length pending) by (simpl in Hi; lia).
      specialize (Hbuf Hsi). simpl in Hbuf.
      replace (sr s + S i) with (S (sr s + i)) in Hbuf by lia.
      rewrite Nat.add_mod_idemp_l in Hbuf by lia.
      rewrite Nat.mod_small in Hbuf.
      * rewrite <- Hbuf. symmetry.
        apply nth_skipn. exact Hi.
      * assert (sr s + i < sr s + length pending) by lia.
        rewrite Hlen in H0. lia.
Qed.

Lemma stop_releases : forall s,
  locked s = true -> locked (stop s) = false.
Proof.
  intros s Hlocked. unfold stop. simpl. reflexivity.
Qed.
