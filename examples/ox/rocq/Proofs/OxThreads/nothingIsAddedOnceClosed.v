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
