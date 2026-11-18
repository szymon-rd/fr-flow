Require Export FrFlowGen.OxThreads.aClosedHerdRefusesToStart.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing set the flag, and it stays set. A call of startThread made after that never sees it unset, so it
    neither adds a thread nor returns. *)
Lemma aClosedHerdRefusesToStart_Proofs_complete : aClosedHerdRefusesToStart_Obl_complete.
Proof.
  intros heldIn history flag [N C] Hsets Hstays Hsees Hmade h code c t from w
    [(from' & response' & to' & Hle & Hclosed) Hstart].
  pose proof (completed_after C Hclosed) as Hlt'.
  pose proof (completed_was_called _ _ _ _ _ _ Hclosed) as Hc.
  pose proof (Hmade h from' ltac:(unfold calledOn; eauto 14)) as Hherd.
  assert (forall m, from <= m -> flag (heldIn L.ThreadHerd_shutdownInProgress h) m) as Hset.
  { intros m Hm. pose proof (Hsets h from' response' to' Hclosed) as Hat.
    assert (to' = m \/ to' < m) as [<- | Hlt] by lia; [exact Hat |].
    apply (Hstays h to' m). split; [split; [| exact Hlt] | exact Hat].
    exact (herd_constructed_later history h from' m ltac:(lia) Hherd). }
  split; intros Hthen.
  - destruct (Hsees h code c t from w (conj Hstart (or_intror Hthen))) as (m & [Hm _] & Hunset).
    apply Hunset, Hset, Hm.
  - destruct (Hsees h code c t from w (conj Hstart (or_introl Hthen))) as (m & [Hm _] & Hunset).
    apply Hunset, Hset, Hm.
Qed.
