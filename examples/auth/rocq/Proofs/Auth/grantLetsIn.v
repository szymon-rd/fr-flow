Require Export FrFlowGen.Auth.grantLetsIn.Spec.

(** A request whose token's holder has a grant for the path is let in on the holder's behalf: what the decision
    says when the holder has one. *)
Lemma grantLetsIn_Proofs_complete : grantLetsIn_Obl_complete.
Proof. intros admit sessions grants hs hd _ t p hg. rewrite (hd hs t p). apply ite_true. exact hg. Qed.
