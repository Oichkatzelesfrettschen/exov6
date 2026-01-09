(* IRQProof - IRQ Queue Ring Buffer Verification *)
(* Rocq Prover 9.x compatible *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Nat.
From Stdlib Require Import Lia.
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
  unfold irq_wait, queue_inv.
  split; [simpl; lia|].
  split; [simpl; lia|].
  exists (skipn 1 pending).
  assert (Hge1: length pending >= 1) by (rewrite Hlen; lia).
  split.
  - rewrite length_skipn. rewrite Hlen. simpl. lia.
  - intros i Hi. cbn [r buf].
    rewrite length_skipn in Hi.
    specialize (Hbuf (S i)).
    assert (Hsi: S i < length pending) by lia.
    specialize (Hbuf Hsi).
    rewrite nth_skipn.
    replace (S (r q) + i) with (r q + S i) by lia.
    exact Hbuf.
Qed.

Lemma irq_trigger_preserves : forall q irq,
  queue_inv q -> w q - r q < IRQ_BUFSZ -> queue_inv (irq_trigger irq q).
Proof.
  intros q irq [Hle [Hbound [pending [Hlen Hbuf]]]] Hspace.
  unfold irq_trigger, queue_inv.
  simpl r. simpl w.
  split. { lia. }
  split. { lia. }
  exists (pending ++ [irq]).
  split.
  - rewrite length_app, Hlen. simpl length. lia.
  - intros i Hi.
    rewrite length_app in Hi. cbn in Hi.
    destruct (le_lt_dec (length pending) i) as [Hi2|Hi2].
    + (* new element at index = length pending *)
      assert (Heq: i = length pending) by lia. subst i.
      rewrite nth_middle.
      assert (Hwr: r q + length pending = w q) by (rewrite Hlen; lia).
      simpl buf.
      rewrite Hwr.
      rewrite Nat.eqb_refl.
      reflexivity.
    + (* old elements: index < length pending *)
      rewrite app_nth1 by lia.
      specialize (Hbuf i Hi2).
      (* Don't simpl buf here - it expands mod to divmod *)
      (* Instead, reason about the if condition directly *)
      destruct (Nat.eqb_spec ((r q + i) mod IRQ_BUFSZ) (w q mod IRQ_BUFSZ)) as [Heqm|Hneq].
      * (* case: indices equal mod IRQ_BUFSZ - derive contradiction *)
        exfalso.
        assert (Hr_i_lt_w: r q + i < w q) by (rewrite Hlen in Hi2; lia).
        assert (Hdiff_pos: 0 < w q - (r q + i)) by lia.
        assert (Hdiff_bound: w q - (r q + i) < IRQ_BUFSZ) by lia.
        (* Set up variables for clarity *)
        set (x := r q + i) in *.
        set (y := w q) in *.
        set (n := IRQ_BUFSZ) in *.
        assert (Hn_pos: n > 0) by (unfold n; lia).
        assert (Hxy: x < y < x + n) by lia.
        (* Key lemma: for x < y < x + n, we have x mod n ≠ y mod n *)
        assert (Hx_mod_bound: x mod n < n) by (apply Nat.mod_upper_bound; lia).
        assert (Hy_mod_bound: y mod n < n) by (apply Nat.mod_upper_bound; lia).
        (* Express y = x + d where 0 < d < n *)
        remember (y - x) as d eqn:Hd_def.
        assert (Hd_range: 0 < d < n) by lia.
        assert (Hy_eq: y = x + d) by lia.
        (* Use add_mod *)
        assert (Hy_mod: y mod n = (x mod n + d mod n) mod n).
        { rewrite Hy_eq. apply Nat.add_mod. lia. }
        (* Since d < n, d mod n = d *)
        rewrite (Nat.mod_small d n) in Hy_mod by lia.
        (* Now analyze the result *)
        destruct (Nat.lt_ge_cases (x mod n + d) n) as [Hlt|Hge].
        -- (* x mod n + d < n, so (x mod n + d) mod n = x mod n + d *)
           assert (Hrhs: (x mod n + d) mod n = x mod n + d).
           { apply Nat.mod_small. exact Hlt. }
           rewrite Hrhs in Hy_mod.
           (* Now Hy_mod: y mod n = x mod n + d, Heqm: x mod n = y mod n *)
           (* So x mod n = x mod n + d, hence d = 0 *)
           lia.
        -- (* x mod n + d >= n *)
           assert (Hsum_bound: x mod n + d < 2 * n) by lia.
           (* Prove (x mod n + d) / n = 1 *)
           assert (Hdiv1: (x mod n + d) / n = 1).
           { symmetry. apply Nat.div_unique with (r := x mod n + d - n).
             - lia. (* x mod n + d - n < n *)
             - lia. (* x mod n + d = n * 1 + (x mod n + d - n) *)
           }
           assert (Hrhs: (x mod n + d) mod n = x mod n + d - n).
           { rewrite Nat.mod_eq; [|lia]. rewrite Hdiv1. lia. }
           rewrite Hrhs in Hy_mod.
           (* Now Hy_mod: y mod n = x mod n + d - n, Heqm: x mod n = y mod n *)
           (* So x mod n = x mod n + d - n, hence d = n, but d < n *)
           lia.
      * (* Hneq: (r q + i) mod IRQ_BUFSZ <> w q mod IRQ_BUFSZ *)
        (* The if condition is false, so the result is buf q ((r q + i) mod IRQ_BUFSZ) *)
        (* Goal: (if X =? Y then irq else buf q X) = nth i pending 0 *)
        (* We have Hbuf: buf q X = nth i pending 0 and Hneq: X <> Y *)
        unfold buf at 1. simpl r. simpl w.
        destruct (Nat.eqb ((r q + i) mod IRQ_BUFSZ) (w q mod IRQ_BUFSZ)) eqn:Heqb.
        -- (* eqb = true, but we have Hneq saying they're not equal - contradiction *)
           apply Nat.eqb_eq in Heqb. contradiction.
        -- (* eqb = false, so we get buf q ((r q + i) mod IRQ_BUFSZ) *)
           exact Hbuf.
Qed.
