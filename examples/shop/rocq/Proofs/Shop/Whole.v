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

(** Of an order already charged: a ledger in which Ann's top-up is posted and its payment claimed. The first step
    of placing `o1`, another order, starts with the top-up charged and claimed. *)

Lemma Whole_Proofs_satisfiable_1_chargeKeepsClaimed : Whole_Obl_satisfiable_1_chargeKeepsClaimed.
Proof.
  unfold Whole_Obl_satisfiable_1_chargeKeepsClaimed.
  exists (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])).
  exists "top-up"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_noStepUndoesAClaim : Whole_Obl_satisfiable_1_noStepUndoesAClaim.
Proof.
  unfold Whole_Obl_satisfiable_1_noStepUndoesAClaim.
  exists (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk [] [])).
  exists "top-up"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30). split; [frflow_evaluate |].
  exists (fun _ => None).
  exists ((Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk [] [])),
    (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk ["o1"%string] []))).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_chargedOnce : Whole_Obl_satisfiable_1_chargedOnce.
Proof.
  unfold Whole_Obl_satisfiable_1_chargedOnce.
  exists (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk [] [])).
  exists "top-up"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30). split; [frflow_evaluate |].
  exists (fun _ => None).
  exists ((Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk [] [])),
    (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk ["o1"%string] []))).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_booksStayOrderly : Whole_Obl_satisfiable_1_booksStayOrderly.
Proof.
  unfold Whole_Obl_satisfiable_1_booksStayOrderly.
  exists (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk [] [])).
  exists "top-up"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30). split; [frflow_evaluate |].
  exists (fun _ => None).
  exists ((Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk [] [])),
    (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk ["o1"%string] []))).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_noStepPostsForAnother : Whole_Obl_satisfiable_1_noStepPostsForAnother.
Proof.
  unfold Whole_Obl_satisfiable_1_noStepPostsForAnother.
  exists (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk [] [])).
  exists "top-up"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30). split; [frflow_evaluate |].
  exists (fun _ => None).
  exists ((Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk [] [])),
    (Checkout_mk (Inventory_mk (Warehouse_mk [Movement_mk "delivery" "tea" 1]))
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])) (OrderBook_mk ["o1"%string] []))).
  frflow_evaluate.
Qed.

(** Of the steps of one charge: the payments over that ledger, charging `o1`. Its first step claims the payment of
    `o1`: the top-up, another order, is claimed where it starts. And charging an order under the top-up's id, whose
    payment is claimed: its one step finds the postings it has, and leaves them. *)

Lemma Whole_Proofs_satisfiable_1_noChargeStepPostsForAnother : Whole_Obl_satisfiable_1_noChargeStepPostsForAnother.
Proof.
  unfold Whole_Obl_satisfiable_1_noChargeStepPostsForAnother.
  exists (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])).
  exists "top-up"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30). split; [frflow_evaluate |].
  exists (fun _ => None).
  exists ((Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])),
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["o1"%string; "top-up"%string]))).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_2_noChargeStepPostsForAnother : Whole_Obl_satisfiable_2_noChargeStepPostsForAnother.
Proof.
  unfold Whole_Obl_satisfiable_2_noChargeStepPostsForAnother.
  exists (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])).
  exists "top-up"%string.
  exists (Order_mk "o1" "ann" "tea" 1 30). split; [frflow_evaluate |].
  exists (fun _ => None).
  exists ((Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])),
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["o1"%string; "top-up"%string]))).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_chargedOnceAmongOthers : Whole_Obl_satisfiable_1_chargedOnceAmongOthers.
Proof.
  unfold Whole_Obl_satisfiable_1_chargedOnceAmongOthers.
  exists (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])).
  exists (Order_mk "o1" "ann" "tea" 1 30).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_2_chargedOnceAmongOthers : Whole_Obl_satisfiable_2_chargedOnceAmongOthers.
Proof.
  unfold Whole_Obl_satisfiable_2_chargedOnceAmongOthers.
  exists (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])).
  exists (Order_mk "o1" "ann" "tea" 1 30). split; [frflow_evaluate |].
  exists (fun _ => None).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_3_chargedOnceAmongOthers : Whole_Obl_satisfiable_3_chargedOnceAmongOthers.
Proof.
  unfold Whole_Obl_satisfiable_3_chargedOnceAmongOthers.
  exists (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])).
  exists (Order_mk "top-up" "ann" "tea" 1 30). split; [frflow_evaluate |].
  exists (fun _ => None).
  exists ((Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string])),
    (Payments_mk (Ledger_mk [Posting_mk "top-up" "ann" 50] ["top-up"%string]))).
  frflow_evaluate.
Qed.
