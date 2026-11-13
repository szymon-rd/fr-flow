Require Export FrFlowGen.Shop.booksStayOrderly.Spec.

(** No step of placing an order leaves an order with postings whose payment is not claimed: the one step that
    touches the ledger is the charge, and the claim on the payments says a charge keeps the books orderly. FrFlow's tactic finds this, given more time than a check gives it: placing an
    order has many ways through. *)
Lemma booksStayOrderly_Proofs_impl : booksStayOrderly_Obl_impl.
Proof.
  frflow_auto.
Qed.
