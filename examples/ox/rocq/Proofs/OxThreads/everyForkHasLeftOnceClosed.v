Require Export FrFlowGen.OxThreads.everyForkHasLeftOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing saw the set empty at a moment. A fork added before it had left by then, or it would have been in the
    set; and none was added after. *)
Lemma everyForkHasLeftOnceClosed_Proofs_complete : everyForkHasLeftOnceClosed_Obl_complete.
Proof.
  intros heldIn history elements [N C] Hends Hnone Hnow Hlive Hmade h t w [Hclosed Hfork].
  destruct Hclosed as [Hcalled Hnotpending].
  destruct (called_and_over_completed history _ _ w Hcalled Hnotpending)
    as (from & response & to & Hdone & Hfw & Htw).
  destruct (Hends h from response to Hdone) as (mm & [Hfm Hmt] & Hempty).
  pose proof (completed_was_called _ _ _ _ _ _ Hdone) as Hc.
  assert (exists m1, m1 < mm /\ calledBy history
    (Invocation_mk "ox.internal.ThreadHerd interruptAllAndJoinUntilCompleted :scala.Unit"%string [h])
    (heldIn "ox.internal.ThreadHerd herdOwner"%string h) m1) as Hclosing
    by (exists from; split; [exact Hfm | exact Hc]).
  assert (madeBefore history h "ox.internal.ThreadHerd"%string mm) as Hherd.
  { apply (made_later history h _ from); [lia |].
    exact (Hmade h from ltac:(unfold calledOn; eauto 14)). }
  destruct (classic (hasLeft heldIn history t h w)) as [H | Hstays]; [exact H | exfalso].
  destruct Hfork as (a & value & to0 & Hto0 & who & Hadd).
  assert (to0 <= mm \/ (mm < to0 /\ mm <= a) \/ (mm < to0 /\ a < mm)) as [Hle | [[Hlt Hge] | [Hlt Hlt']]] by lia.
  - (* its add had returned by the moment the set is empty: it is in the set, or has left *)
    apply (Hempty t). apply (Hlive h t mm). split; [exact Hherd | split].
    + exists a, value, to0. split; [exact Hle | exists who; exact Hadd].
    + intros (r & Hr & Hrem). apply Hstays. exists r. split; [lia | exact Hrem].
  - (* its add was made from that moment on *)
    apply (Hnone h t mm a); [| exists who; exact (completed_was_called _ _ _ _ _ _ Hadd)].
    split; [split; [exact Hclosing | exact Hempty] | exact Hge].
  - (* its add was in progress at that moment *)
    destruct (still_pending mm C Hadd Hlt' Hlt) as (Ham & Hb & Hn).
    apply (Hnow h t mm (conj Hclosing Hempty)). right. exists a. split; [exact Ham | exists who; split; assumption].
Qed.

(** Its parts can hold together: a run in which nothing happens meets each. *)
Lemma everyForkHasLeftOnceClosed_Proofs_feasible : everyForkHasLeftOnceClosed_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ _ => False).
  split; [exact rest_runs |].
  split.
  { intros h from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h t m w [[(m1 & _ & H) _] _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h t m [(m1 & _ & H) _]. destruct (nothing_called_at_rest _ _ _ H). }
  split.
  { intros h t w [(m & by_ & ins & hs & _ & H) _]. discriminate H. }
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
