Require Export FrFlowGen.FullShortener.removeKeepsOtherCodes.Spec.
Require Export Proofs.FullShortener.Lemmas.

(** Removing a code changes where no other code leads: filtering out the links of one code leaves the first link
    of any other where it was. *)
Lemma removeKeepsOtherCodes_Proofs_impl : removeKeepsOtherCodes_Obl_impl.
Proof.
  unfold removeKeepsOtherCodes_Obl_impl, removeKeepsOtherCodes_claim.
  intros s c d cd. rewrite Lemmas_resolve_removed. unfold retiringLinks_resolve, decide. cbn.
  rewrite (Lemmas_find_filter_other _ c d cd). reflexivity.
Qed.
