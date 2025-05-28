Record lambda_cap := { consumed : bool }.

Definition lambda_cap_use (lc : lambda_cap) : lambda_cap * bool :=
  if consumed lc then (lc, false)
  else ({| consumed := true |}, true).

Definition lambda_cap_delegate (lc : lambda_cap) : lambda_cap * bool :=
  if consumed lc then (lc, false)
  else (lc, true).

Definition lambda_cap_revoke (lc : lambda_cap) : lambda_cap * bool :=
  if consumed lc then (lc, false)
  else ({| consumed := true |}, true).

Lemma use_consumes : forall lc lc' r,
  lambda_cap_use lc = (lc', r) ->
  r = true ->
  consumed lc' = true.
Proof.
  intros lc lc' r H Hsucc.
  destruct lc as [b].
  simpl in H.
  destruct b; inversion H; subst; auto.
Qed.

Lemma use_fail_if_consumed : forall lc lc' r,
  consumed lc = true ->
  lambda_cap_use lc = (lc', r) ->
  r = false /\ lc' = lc.
Proof.
  intros [b] lc' r Hb H.
  simpl in Hb, H.
  subst b.
  simpl in H.
  now inversion H.
Qed.

Theorem use_once : forall lc lc1 r1 lc2 r2,
  lambda_cap_use lc = (lc1, r1) ->
  r1 = true ->
  lambda_cap_use lc1 = (lc2, r2) ->
  r2 = false.
Proof.
  intros lc lc1 r1 lc2 r2 Huse1 Hsucc1 Huse2.
  apply use_consumes in Huse1; auto.
  subst lc1.
  apply use_fail_if_consumed in Huse2; auto.
  destruct Huse2 as [Hfail _].
  exact Hfail.
Qed.

Lemma delegate_no_consume : forall lc lc' r,
  consumed lc = false ->
  lambda_cap_delegate lc = (lc', r) ->
  r = true /\ lc' = lc /\ consumed lc' = false.
Proof.
  intros [b] lc' r Hb H.
  simpl in Hb, H.
  subst b.
  simpl in H.
  inversion H; subst; auto.
Qed.

Theorem delegate_preserves_single_use : forall lc lc1 r1 lc2 r2 lc3 r3,
  consumed lc = false ->
  lambda_cap_delegate lc = (lc1, r1) ->
  r1 = true ->
  lambda_cap_use lc1 = (lc2, r2) ->
  r2 = true ->
  lambda_cap_use lc2 = (lc3, r3) ->
  r3 = false.
Proof.
  intros lc lc1 r1 lc2 r2 lc3 r3 Hconsumed Hdel Hdelok Huse1 Husk Huse2.
  apply delegate_no_consume in Hdel; auto.
  destruct Hdel as [_ [Heq _]].
  subst lc1.
  eapply use_once; eauto.
Qed.
