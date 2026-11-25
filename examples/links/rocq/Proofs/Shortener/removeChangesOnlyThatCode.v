Require Export FrFlowGen.Shortener.removeChangesOnlyThatCode.Spec.
Require Export Proofs.Shortener.Lemmas.

(** What removing does, exactly, from its two cases: the removed code leads nowhere, and any other where it did. *)
Lemma removeChangesOnlyThatCode_Proofs_impl : removeChangesOnlyThatCode_Obl_impl.
Proof.
  unfold removeChangesOnlyThatCode_Obl_impl, removeChangesOnlyThatCode_claim, removedCodeLeadsNowhere_claim,
    removeKeepsOtherCodes_claim.
  intros nowhere others s c d.
  destruct (classic (d = c)) as [e | e].
  - rewrite (ite_true _ _ _ e). subst d. specialize (nowhere s c).
    destruct (retiringLinks_resolve (snd (retiringLinks_remove s c)) c); [contradiction | reflexivity].
  - rewrite (ite_false _ _ _ e). apply others. intros h. apply e. symmetry. exact h.
Qed.
