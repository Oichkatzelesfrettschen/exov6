Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Import ListNotations.

(* Ring buffer size as used in irq.c *)
Definition IRQ_BUFSZ := 32%nat.

(* Abstract queue state. [buf] models the circular buffer contents,
   while [r] and [w] are the read/write indices. *)
Record irq_queue := {
  buf : nat -> nat;
  r : nat;
  w : nat
}.

(* Invariant describing a valid queue while the lock is held.  The
   second clause captures that all pending values appear in [buf] at
   the expected modulo positions. *)
Definition queue_inv (q : irq_queue) : Prop :=
  r q <= w q /\
  w q - r q <= IRQ_BUFSZ /\
  exists pending,
    length pending = w q - r q /\
    forall i, i < length pending ->
      buf q ((r q + i) mod IRQ_BUFSZ) = nth i pending 0.

(* [irq_wait] simply increments [r] after reading an element. *)
Definition irq_wait (q : irq_queue) : irq_queue :=
  {| buf := buf q; r := S (r q); w := w q |}.

(* [irq_trigger] writes the new irq at the current [w] position and
   increments the write index. *)
Definition irq_trigger (irq : nat) (q : irq_queue) : irq_queue :=
  {| buf := fun k => if Nat.eqb k (w q mod IRQ_BUFSZ) then irq else buf q k;
     r := r q;
     w := S (w q) |}.

Lemma irq_wait_preserves : forall q,
  queue_inv q -> r q < w q -> queue_inv (irq_wait q).
Proof.
  intros q [Hle [Hbound [pending [Hlen Hbuf]]]] Hlt.
  unfold irq_wait.
  repeat split.
  - lia.
  - lia.
  - exists (skipn 1 pending).  (* drop the first element *)
    assert (Hlen': length pending = w q - r q) by auto.
    assert (length pending >= 1) by (rewrite Hlen; lia).
    rewrite skipn_length; [|lia].
    split.
    + rewrite Hlen. simpl. lia.
    + intros i Hi.
      specialize (Hbuf (S i)).
      assert (Hsi: S i < length pending) by (simpl in Hi; lia).
      specialize (Hbuf Hsi). simpl in Hbuf.
      replace (r q + S i) with (S (r q + i)) in Hbuf by lia.
      rewrite Nat.add_mod_idemp_l in Hbuf by lia.
      rewrite Nat.mod_small in Hbuf.
      * rewrite <- Hbuf. symmetry.
        apply nth_skipn. exact Hi.
      * assert (r q + i < r q + length pending) by lia.
        rewrite Hlen in H0. lia.
Qed.

Lemma irq_trigger_preserves : forall q irq,
  queue_inv q -> w q - r q < IRQ_BUFSZ -> queue_inv (irq_trigger irq q).
Proof.
  intros q irq [Hle [Hbound [pending [Hlen Hbuf]]]] Hspace.
  unfold irq_trigger.
  repeat split.
  - lia.
  - lia.
  - exists (pending ++ [irq]).
    split.
    + rewrite app_length Hlen. simpl. lia.
    + intros i Hi.
      apply lt_n_Sm_le in Hi.
      destruct (le_lt_dec (length pending) i) as [Hi2|Hi2].
      * (* new element *)
        assert (i = length pending) by lia. subst i.
        rewrite nth_app_right; [|rewrite Hlen; lia].
        rewrite Nat.sub_diag. simpl.
        rewrite Nat.add_mod_idemp_l by lia.
        rewrite Nat.mod_small.
        -- now simpl; rewrite Nat.eqb_refl.
           reflexivity.
        -- rewrite Hlen. lia.
      * (* old elements *)
        assert (i < length pending) by lia.
        rewrite nth_app_left; [|lia].
        specialize (Hbuf i H0).
        rewrite Nat.add_mod_idemp_l in Hbuf by lia.
        rewrite Nat.mod_small in Hbuf.
        -- assumption.
        -- assert (r q + i < r q + length pending) by lia.
           rewrite Hlen in H1. lia.
Qed.

