Require Export FrFlowGen.OxThreads.everyForkHasLeftOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing saw the set empty at a moment. A fork added before it had left by then, or it would have been in the
    set; and none was added after. *)
Lemma everyForkHasLeftOnceClosed_Proofs_complete : everyForkHasLeftOnceClosed_Obl_complete.
Proof.
  intros heldIn history elements Hends Hnone Hlive h t w [Hclosed Hfork].
  destruct Hclosed as [Hcalled Hnotpending].
  destruct (called_and_over_completed history _ _ w Hcalled Hnotpending) as (from & response & to & Hdone & Hfw & Htw).
  destruct (Hends h from response to Hdone) as (mm & [Hfm Hmt] & Hempty).
  destruct (classic (hasLeft heldIn history t h w)) as [H | Hstays]; [exact H | exfalso].
  destruct Hfork as (a & Ha & who & Hadd).
  assert (a < mm \/ mm <= a) as [Hlt | Hge] by lia.
  - apply (Hempty t). apply (Hlive h t mm). split.
    + exists a. split; [exact Hlt | exists who; exact Hadd].
    + intros (r & Hr & Hrem). apply Hstays. exists r. split; [lia | exact Hrem].
  - apply (Hnone h t mm a); [| exists who; exact Hadd]. split; [split; [| exact Hempty] | exact Hge].
    exists from. split; [exact Hfm | exact (completed_was_called _ _ _ _ _ _ Hdone)].
Qed.

(** Its parts can hold together: a run in which nothing happens meets each. *)
Lemma everyForkHasLeftOnceClosed_Proofs_feasible : everyForkHasLeftOnceClosed_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ _ => False).
  split.
  { intros h from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  split.
  { intros h t m w _ (who & H). destruct (nothing_called_at_rest _ _ _ H). }
  intros h t w [H _]. destruct (no_fork_at_rest _ _ _ _ H).
Qed.
