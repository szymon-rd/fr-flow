Require Export FrFlowGen.OxThreads.everyForkHasLeftOnceClosed.Spec.
Require Export Proofs.OxThreads.Lemmas.

(** Closing saw the set empty at a moment. A fork added before it had left by then, or it would have been in the
    set; and none was added after. *)
Lemma everyForkHasLeftOnceClosed_Proofs_complete : everyForkHasLeftOnceClosed_Obl_complete.
Proof.
  intros heldIn steps elements Hends Hnone Hlive h t w [Hclosed Hfork].
  destruct Hclosed as [Hcalled Hnotpending].
  destruct (called_and_over_completed steps _ _ w Hcalled Hnotpending) as (from & answer & to & Hdone & Hfw & Htw).
  destruct (Hends h from answer to Hdone) as (mm & [Hfm Hmt] & Hempty).
  destruct (classic (hasLeft heldIn steps t h w)) as [H | Hstays]; [exact H | exfalso].
  destruct Hfork as (a & Ha & who & Hadd).
  assert (a < mm \/ mm <= a) as [Hlt | Hge] by lia.
  - apply (Hempty t). apply (Hlive h t mm). split.
    + exists a. split; [exact Hlt | exists who; exact Hadd].
    + intros (r & Hr & Hrem). apply Hstays. exists r. split; [lia | exact Hrem].
  - apply (Hnone h t mm a); [| exists who; exact Hadd]. split; [split; [| exact Hempty] | exact Hge].
    exists from. split; [exact Hfm | exact (completed_was_called _ _ _ _ _ _ Hdone)].
Qed.
