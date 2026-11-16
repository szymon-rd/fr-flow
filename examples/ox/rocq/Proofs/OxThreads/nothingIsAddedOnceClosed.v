Require Export FrFlowGen.OxThreads.nothingIsAddedOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing saw the set empty at a moment after it was called, and nothing is added from then on. *)
Lemma nothingIsAddedOnceClosed_Proofs_complete : nothingIsAddedOnceClosed_Obl_complete.
Proof.
  intros heldIn history elements _ Hends Hnone h t w (from & response & to & Htw & Hdone).
  destruct (Hends h from response to Hdone) as (mm & [Hfm Hmt] & Hempty).
  apply (Hnone h t mm w). split; [split; [| exact Hempty] | lia].
  exists from. split; [exact Hfm | exact (completed_was_called _ _ _ _ _ _ Hdone)].
Qed.

(** Its parts can hold together: a run in which nothing happens meets each. *)
Lemma nothingIsAddedOnceClosed_Proofs_feasible : nothingIsAddedOnceClosed_Obl_feasible.
Proof.
  exists (fun _ x => x), (fun _ => Event_Stutter), (fun _ _ _ => False).
  split; [exact rest_runs |].
  split.
  { intros h from response to H. destruct (nothing_completed_at_rest _ _ _ _ _ H). }
  intros h t m w _ (who & H). destruct (nothing_called_at_rest _ _ _ H).
Qed.
