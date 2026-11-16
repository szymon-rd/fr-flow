Require Export FrFlowGen.OxThreads.aClosedHerdRefusesToStart.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing set the flag, and it stays set. A call of startThread made after that never sees it unset, so it
    neither adds a thread nor returns. *)
Lemma aClosedHerdRefusesToStart_Proofs_complete : aClosedHerdRefusesToStart_Obl_complete.
Proof.
  intros heldIn history flag _ Hsets Hstays Hsees Hmade h code c t from w [[Hcalled Hnotpending] Hstart].
  destruct (called_and_over_completed history _ _ from Hcalled Hnotpending)
    as (from' & response' & to' & Hclosed & Hlt' & Hle).
  pose proof (completed_was_called _ _ _ _ _ _ Hclosed) as Hc.
  pose proof (Hmade h from' ltac:(unfold calledOn; eauto 14)) as Hherd.
  assert (forall m, from <= m -> flag (heldIn "ox.internal.ThreadHerd shutdownInProgress"%string h) m) as Hset.
  { intros m Hm. pose proof (Hsets h from' response' to' Hclosed) as Hat.
    assert (to' = m \/ to' < m) as [<- | Hlt] by lia; [exact Hat |].
    apply (Hstays h to' m). split; [split; [| exact Hlt] | exact Hat].
    destruct Hherd as (x & maker & since & by_then & Hthen & Hherd).
    exists x, maker, since, by_then. split; [lia | exact Hherd]. }
  split; intros Hthen.
  - destruct (Hsees h code c t from w (conj Hstart (or_intror Hthen))) as (m & [Hm _] & Hunset).
    apply Hunset, Hset, Hm.
  - destruct (Hsees h code c t from w (conj Hstart (or_introl Hthen))) as (m & [Hm _] & Hunset).
    apply Hunset, Hset, Hm.
Qed.

(** Its parts can hold together: a run in which nothing happens, of flags never set, meets each. *)
Lemma aClosedHerdRefusesToStart_Proofs_feasible : aClosedHerdRefusesToStart_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ => False).
  split; [exact rest_runs |].
  split.
  { intros h from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h a b [_ H]. exact H. }
  split.
  { intros h code c t from w [H _]. destruct (nothing_called_at_rest _ _ _ H). }
  intros h w H. repeat (destruct H as [H | H]); destruct (nothing_called_on_at_rest _ _ _ H).
Qed.
