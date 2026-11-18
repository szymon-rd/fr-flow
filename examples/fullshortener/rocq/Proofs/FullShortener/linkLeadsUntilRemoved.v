Require Export FrFlowGen.FullShortener.linkLeadsUntilRemoved.Spec.

(** A link leads to its URL until it is removed, by induction over the calls made later: each is a URL shortened,
    which does not move an existing code, or another code removed, which moves no other. *)
Lemma linkLeadsUntilRemoved_Proofs_impl : linkLeadsUntilRemoved_Obl_impl.
Proof.
  unfold linkLeadsUntilRemoved_Obl_impl, linkLeadsUntilRemoved_claim, shortenKeepsExistingLinks_claim,
    removeKeepsOtherCodes_claim.
  intros kept others s code url later. revert s.
  induction later as [| call rest ih]; intros s [leads never].
  - exact leads.
  - rewrite List_foldl_cons. apply ih. split.
    + pose proof (never call (or_introl eq_refl)) as allowed.
      destruct call as [given | other]; cbv beta iota.
      * rewrite kept; [exact leads | rewrite leads; discriminate].
      * rewrite others; [exact leads | exact allowed].
    + intros later_call among. apply never. right. exact among.
Qed.
