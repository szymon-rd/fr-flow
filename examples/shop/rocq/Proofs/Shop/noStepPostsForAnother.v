Require Export FrFlowGen.Shop.noStepPostsForAnother.Spec.

(** No step of placing an order makes a posting of another order: the one step that touches the ledger is the
    charge, and the claim on the payments says a charge posts for no other order. FrFlow's tactic finds this, given more time than a check gives it: placing an
    order has many ways through. *)
Lemma noStepPostsForAnother_Proofs_impl : noStepPostsForAnother_Obl_impl.
Proof.
  frflow_auto.
Qed.
