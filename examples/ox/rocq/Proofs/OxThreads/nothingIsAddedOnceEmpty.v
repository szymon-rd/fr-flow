Require Export FrFlowGen.OxThreads.nothingIsAddedOnceEmpty.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Who adds a thread is calling startThread, so is inside: the owner, who has not called closing; or a fork that
    has not left, which is in the set if it was added before the set was empty, and was not added after. *)
Lemma nothingIsAddedOnceEmpty_Proofs_complete : nothingIsAddedOnceEmpty_Obl_complete.
Proof.
  intros heldIn history elements [N C] Hnow Hlive Hstay Honly Hmade h t m w [[Hclosing Hempty] Hmw].
  pose proof Hclosing as (m1 & Hm1 & Hc1).
  pose proof (herd_constructed_later history h m1 m ltac:(lia)
    (Hmade h m1 ltac:(unfold calledOn; eauto 14))) as Hherd.
  revert t. pattern w. apply (Zlt_lower_bound_ind _ m); [| exact Hmw].
  intros x IH Hx t (who & Hadd).
  destruct (Honly h t who x m (conj Hherd Hadd)) as [(code & m0 & Hm0 & Hbegun & Hpending) _].
  assert (inside heldIn history who h x) as Hin.
  { apply (Hstay h code who x). right. exists m0. split; [exact Hm0 | split; [exact Hbegun | exact Hpending]]. }
  destruct Hin as [[Hown Hnot] | [(a & value & to & Hto & who' & Hdone) Hstays]].
  - apply Hnot. exists m1. split; [lia | exact Hc1].
  - assert (to <= m \/ (m < to /\ m <= a) \/ (m < to /\ a < m)) as [Hle | [[Hlt Hge] | [Hlt Hlt']]] by lia.
    + (* its add had returned by the moment the set is empty: it is in the set *)
      apply (Hempty who). apply (Hlive h who m). split; [exact Hherd | split].
      * exists a, value, to. split; [exact Hle | exists who'; exact Hdone].
      * intros (r & Hr & Hrem). apply Hstays. exists r. split; [lia | exact Hrem].
    + (* its add was made from that moment on, before this one *)
      pose proof (completed_after C Hdone) as Hat.
      apply (IH a ltac:(lia) who). exists who'. exact (completed_was_called _ _ _ _ _ _ Hdone).
    + (* its add was in progress at that moment *)
      destruct (still_pending m C Hdone Hlt' Hlt) as (Ham & Hb & Hn).
      apply (Hnow h who m (conj Hclosing Hempty)). right. exists a. split; [exact Ham | exists who'; split; assumption].
Qed.

(** Its parts can hold together: a run in which nothing happens meets each. *)
