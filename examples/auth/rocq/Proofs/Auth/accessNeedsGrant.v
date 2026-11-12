Require Export FrFlowGen.Auth.accessNeedsGrant.Spec.

(** A request is let in on behalf of a user only with a grant naming them and the path: the decision lets in the
    token's holder only when they have one. *)
Lemma accessNeedsGrant_Proofs_complete : accessNeedsGrant_Obl_complete.
Proof.
  intros admit grants sessions hs hd t p u hu. rewrite (hd hs t p) in hu.
  destruct (classic (holderGranted sessions grants t p)) as [hg | hg].
  - rewrite (ite_true _ _ _ hg) in hu. destruct hg as [v [hv hgv]]. rewrite hv in hu.
    injection hu as ->. exact hgv.
  - rewrite (ite_false _ _ _ hg) in hu. discriminate.
Qed.
