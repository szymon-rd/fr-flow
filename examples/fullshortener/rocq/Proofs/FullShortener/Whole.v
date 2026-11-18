Require Export FrFlowGen.FullShortener.Whole.Spec.

(** The condition of the first promise FrFlow's search found no values for, shown to hold of values given here: in
    a shortener whose one link leads code 0 home, code 0 leads there, and no call made later removes it when none
    is made. *)
Lemma Whole_Proofs_satisfiable_1_linkLeadsUntilRemoved : Whole_Obl_satisfiable_1_linkLeadsUntilRemoved.
Proof.
  unfold Whole_Obl_satisfiable_1_linkLeadsUntilRemoved.
  exists (Links_mk [Link_mk (Code_mk 0) (Url_mk "home")] []). exists (Code_mk 0). exists (Url_mk "home").
  exists [].
  frflow_evaluate.
Qed.
