Require Export FrFlowGen.OxThreads.nothingIsAddedOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing saw the set empty at a moment after it was called, and nothing is added from then on. *)
Lemma nothingIsAddedOnceClosed_Proofs_complete : nothingIsAddedOnceClosed_Obl_complete.
Proof.
  intros heldIn steps elements Hends Hnone h t w [Hcalled Hnotpending].
  destruct (called_and_over_completed steps _ _ w Hcalled Hnotpending) as (from & answer & to & Hdone & Hfw & Htw).
  destruct (Hends h from answer to Hdone) as (mm & [Hfm Hmt] & Hempty).
  apply (Hnone h t mm w). split; [split; [| exact Hempty] | lia].
  exists from. split; [exact Hfm | exact (completed_was_called _ _ _ _ _ _ Hdone)].
Qed.
