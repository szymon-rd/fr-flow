Require Export FrFlowGen.Shortener.removedCodeNotReissued.Spec.
Require Export Proofs.Shortener.Lemmas.

(** A code just removed is not given to the next URL shortened: no link of it is left to give again, and a new
    code is none of the codes removed. *)
Lemma removedCodeNotReissued_Proofs_impl : removedCodeNotReissued_Obl_impl.
Proof.
  unfold removedCodeNotReissued_Obl_impl, removedCodeNotReissued_claim.
  intros s c u. rewrite Lemmas_remove.
  destruct (Lemmas_shorten_cases (Links_mk (List_filter (fun l => ~ Link_code l = c) (Links_issued s))
    (c :: Links_retired s)) u) as [[l [i [_ e]]] | [_ [k [fresh e]]]]; rewrite e; cbn [fst].
  - cbn [Links_issued] in i. apply List_filter_In in i. destruct i as [_ h]. exact h.
  - apply fresh. apply in_or_app. right. left. reflexivity.
Qed.
