Require Export FrFlowGen.Shortener.removedCodeLeadsNowhere.Spec.
Require Export Proofs.Shortener.Lemmas.

(** A removed code leads nowhere: every link of it is filtered out, so none is found. *)
Lemma removedCodeLeadsNowhere_Proofs_impl : removedCodeLeadsNowhere_Obl_impl.
Proof.
  unfold removedCodeLeadsNowhere_Obl_impl, removedCodeLeadsNowhere_claim.
  intros s c. rewrite Lemmas_remove. unfold retiringLinks_resolve, decide. cbn.
  rewrite Lemmas_find_filter_same. exact I.
Qed.
