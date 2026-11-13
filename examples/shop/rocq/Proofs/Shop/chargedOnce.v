Require Export FrFlowGen.Shop.chargedOnce.Spec.

(** No step of placing an order adds to the postings of an order already charged, its payment claimed: the one
    step that touches the ledger is the charge, and the claim on the payments says a charge posts for no order whose
    payment is claimed. FrFlow's tactic finds this, given more time than a check gives it: placing an
    order has many ways through. *)
Lemma chargedOnce_Proofs_impl : chargedOnce_Obl_impl.
Proof.
  frflow_auto.
Qed.
