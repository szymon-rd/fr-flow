Require Export FrFlowGen.OxThreads.everyForkHasLeftOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing saw the set empty at a moment. A fork added before it had left by then, or it would have been in the
    set; and none was added after. *)
Lemma everyForkHasLeftOnceClosed_Proofs_complete : everyForkHasLeftOnceClosed_Obl_complete.
Proof.
  intros heldIn history elements [N C] Hends Hnone Hnow Hlive Hmade h t w [Hclosed Hfork].
  destruct Hclosed as (from & response & to & Htw & Hdone).
  pose proof (completed_after C Hdone) as Hfw.
  destruct (Hends h from response to Hdone) as (mm & [Hfm Hmt] & Hempty).
  pose proof (completed_was_called _ _ _ _ _ _ Hdone) as Hc.
  assert (exists m1, m1 < mm /\ calledBy history
    (Invocation_mk L.ThreadHerd_interruptAllAndJoinUntilCompleted [h])
    (heldIn L.ThreadHerd_herdOwner h) m1) as Hclosing
    by (exists from; split; [exact Hfm | exact Hc]).
  pose proof (herd_constructed_later history h from mm ltac:(lia)
    (Hmade h from ltac:(unfold calledOn; eauto 14))) as Hherd.
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
