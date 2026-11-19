Require Export FrFlowGen.FullShortener.removedLinkStaysRemoved.Spec.

(** A removed link never leads anywhere again, by induction over the calls made later, from the last: a URL
    shortened is not given the removed code, so it moves no other; removing the code again leaves it leading
    nowhere; and removing another code moves no other. *)
Lemma removedLinkStaysRemoved_Proofs_impl : removedLinkStaysRemoved_Obl_impl.
Proof.
  unfold removedLinkStaysRemoved_Obl_impl, removedLinkStaysRemoved_claim, removeKeepsOtherCodes_claim,
    removedCodeLeadsNowhere_claim, removedCodeNotReissued_claim, shortenChangesOnlyItsCode_claim.
  intros only nowhere others notGiven s code later.
  induction later as [| call earlier ih] using rev_ind.
  - exact (nowhere s code).
  - rewrite List_foldl_app. rewrite List_foldl_cons. rewrite List_foldl_nil.
    destruct call as [given | other].
    + rewrite only; [exact ih |].
      intros e. apply (notGiven s code given earlier). symmetry. exact e.
    + destruct (classic (other = code)) as [e | e].
      * subst other. apply nowhere.
      * rewrite others; [exact ih | exact e].
Qed.
