Require Export FrFlowGen.Payments.Whole.Spec.

(** Two of the conditions of the payment stream's claims FrFlow's search found no values for, each shown to hold.
    Of the ledger: one in which the payment `p1` is marked has it posted. Of the handler: one in which `p1`, of 30
    on a card with a limit of 100, is decided, approved and marked as posted. *)

Lemma Whole_Proofs_satisfiable_1_postKeepsPosted : Whole_Obl_satisfiable_1_postKeepsPosted.
Proof.
  unfold Whole_Obl_satisfiable_1_postKeepsPosted.
  exists (Ledger_mk [] ["p1"%string]).
  exists "p1"%string.
  exists (Payment_mk 0 "p1" "card" "shop" 30 1).
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_appliedStaysApplied : Whole_Obl_satisfiable_1_appliedStaysApplied.
Proof.
  unfold Whole_Obl_satisfiable_1_appliedStaysApplied.
  exists (PaymentHandler_mk (CardLimits_mk 100 [Decision_mk "p1" "card" 1 30 True]) (Ledger_mk [] ["p1"%string])
    (ConsumerOffsets_mk 0)).
  exists "p1"%string.
  exists (Payment_mk 0 "p1" "card" "shop" 30 1).
  repeat (autounfold with frflow_defs in *; intros). cbn. repeat split; eauto 8.
Qed.
