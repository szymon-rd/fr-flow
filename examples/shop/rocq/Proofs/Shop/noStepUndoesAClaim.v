Require Export FrFlowGen.Shop.noStepUndoesAClaim.Spec.

(** No step of placing an order undoes the claim of a payment: the one step that touches the ledger is the
    charge, and the claim on the payments says a charge leaves every payment claimed that was. FrFlow's tactic finds this, given more time than a check gives it: placing an
    order has many ways through. *)
Lemma noStepUndoesAClaim_Proofs_impl : noStepUndoesAClaim_Obl_impl.
Proof.
  frflow_auto.
Qed.
