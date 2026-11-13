Require Export FrFlowGen.Shop.Whole.Spec.

(** The conditions of the shop's claims FrFlow's search found no values for, each shown to hold of values given
    here: a warehouse with one unit of tea, a ledger in which Ann holds 50, and her order `o1` of one unit of tea
    for 30. The warehouse holds the units, the ledger charges her, the payments and the inventory over them do
    the same, and the checkout over those confirms the order; its first step, registering the order, starts with
    nothing oversold and nobody overdrawn. `frflow_evaluate` runs the code on them. *)

Lemma Whole_Proofs_satisfiable_1_heldUnitsAreTaken : Whole_Obl_satisfiable_1_heldUnitsAreTaken.
Proof.
  unfold Whole_Obl_satisfiable_1_heldUnitsAreTaken.
  exists (Warehouse_mk [Movement_mk "delivery" "tea" 1]).
  exists "tea"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_chargeMovesTheAmount : Whole_Obl_satisfiable_1_chargeMovesTheAmount.
Proof.
  unfold Whole_Obl_satisfiable_1_chargeMovesTheAmount.
  exists (Ledger_mk [Posting_mk "top-up" "ann" 50] []).
  exists "ann"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_releaseUndoesReserve : Whole_Obl_satisfiable_1_releaseUndoesReserve.
Proof.
  unfold Whole_Obl_satisfiable_1_releaseUndoesReserve.
  exists (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1])).
  exists "tea"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_doneChargePays : Whole_Obl_satisfiable_1_doneChargePays.
Proof.
  unfold Whole_Obl_satisfiable_1_doneChargePays.
  exists (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] [])).
  exists "ann"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_confirmedIsPaid : Whole_Obl_satisfiable_1_confirmedIsPaid.
Proof.
  unfold Whole_Obl_satisfiable_1_confirmedIsPaid.
  exists (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] [])) (OrderBook_mk [] [])).
  exists "ann"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_neverOversold : Whole_Obl_satisfiable_1_neverOversold.
Proof.
  unfold Whole_Obl_satisfiable_1_neverOversold.
  exists (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] [])) (OrderBook_mk [] [])).
  exists "tea"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30). split; [frflow_evaluate |].
  exists (fun _ => None).
  exists ((Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] [])) (OrderBook_mk [] [])),
    (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] [])) (OrderBook_mk ["o1"%string] []))).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_neverOverdrawn : Whole_Obl_satisfiable_1_neverOverdrawn.
Proof.
  unfold Whole_Obl_satisfiable_1_neverOverdrawn.
  exists (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] [])) (OrderBook_mk [] [])).
  exists "ann"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30). split; [frflow_evaluate |].
  exists (fun _ => None).
  exists ((Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] [])) (OrderBook_mk [] [])),
    (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] [])) (OrderBook_mk ["o1"%string] []))).
  frflow_evaluate.
Qed.
