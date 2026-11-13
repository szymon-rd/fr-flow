Require Export FrFlowGen.Shop.neverOversold.Spec.

(** No step of placing an order leaves anything oversold that was not: each step is one call of the inventory, the
    payments or the order book, and the claims on them say each call keeps it. FrFlow's tactic finds this, given
    more time than a check gives it: placing an order has many ways through. *)
Lemma neverOversold_Proofs_impl : neverOversold_Obl_impl.
Proof.
  frflow_auto.
Qed.
