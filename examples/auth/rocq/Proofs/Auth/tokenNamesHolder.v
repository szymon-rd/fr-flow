Require Export FrFlowGen.Auth.tokenNamesHolder.Spec.

(** A request is let in only on behalf of the user its token was issued to: the decision lets in only the
    token's holder. *)
Lemma tokenNamesHolder_Proofs_complete : tokenNamesHolder_Obl_complete.
Proof.
  intros admit sessions grants hs hd _ t p u hu. rewrite (hd hs t p) in hu.
  destruct (classic (holderGranted sessions grants t p)) as [hg | hg].
  - rewrite (ite_true _ _ _ hg) in hu. exact hu.
  - rewrite (ite_false _ _ _ hg) in hu. discriminate.
Qed.
