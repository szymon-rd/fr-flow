Require Export FrFlowGen.FullShortener.shortenChangesOnlyItsCode.Spec.
Require Export Proofs.FullShortener.Lemmas.

(** Shortening changes where no code leads but the one it gives: a code given again changes nothing, and a new
    code's link is put first, where only that code finds it. *)
Lemma shortenChangesOnlyItsCode_Proofs_impl : shortenChangesOnlyItsCode_Obl_impl.
Proof.
  unfold shortenChangesOnlyItsCode_Obl_impl, shortenChangesOnlyItsCode_claim.
  intros s u d.
  destruct (Lemmas_shorten_cases s u) as [[l [_ [_ e]]] | [_ [k [_ e]]]]; rewrite e; cbn [fst snd]; intros ne;
    [reflexivity |].
  rewrite Lemmas_resolve_cons.
  assert (h : ~ k = d) by (intros kd; apply ne; symmetry; exact kd).
  rewrite (ite_false _ _ _ h). reflexivity.
Qed.
