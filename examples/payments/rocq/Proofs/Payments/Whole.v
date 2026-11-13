Require Export FrFlowGen.Payments.Whole.Spec.

(** The conditions of the payment stream's claims FrFlow's search found no values for, each shown to hold of values
    given here. Of the ledger: one in which the payment `p1` is marked has it posted. Of the handler: one in which
    `p1`, of 30 on a card with a limit of 100, is decided, approved and marked as posted, handling `p1` again while
    no other call does anything; its first step starts from that handler and leaves it as it was. `frflow_evaluate`
    runs the handler's code on them. *)

Definition settled : PaymentHandler :=
  PaymentHandler_mk (CardLimits_mk 100 [Decision_mk "p1" "card" 1 30 True]) (Ledger_mk [] ["p1"%string])
    (ConsumerOffsets_mk 0).
Definition again : Payment := Payment_mk 0 "p1" "card" "shop" 30 1.

Lemma Whole_Proofs_satisfiable_1_postKeepsPosted : Whole_Obl_satisfiable_1_postKeepsPosted.
Proof.
  unfold Whole_Obl_satisfiable_1_postKeepsPosted.
  exists (Ledger_mk [] ["p1"%string]). exists "p1"%string. exists again. unfold again.
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_appliedStaysApplied : Whole_Obl_satisfiable_1_appliedStaysApplied.
Proof.
  unfold Whole_Obl_satisfiable_1_appliedStaysApplied.
  exists settled. exists "p1"%string. exists again. unfold settled, again.
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_everyStepKeepsWithinLimit : Whole_Obl_satisfiable_1_everyStepKeepsWithinLimit.
Proof.
  unfold Whole_Obl_satisfiable_1_everyStepKeepsWithinLimit.
  exists settled. exists "card"%string. exists 1. exists again. exists (fun _ => None). exists (settled, settled).
  unfold settled, again.
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_noStepPostsTwice : Whole_Obl_satisfiable_1_noStepPostsTwice.
Proof.
  unfold Whole_Obl_satisfiable_1_noStepPostsTwice.
  exists settled. exists "p1"%string. exists again. exists (fun _ => None). exists (settled, settled).
  unfold settled, again.
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_1_everyStepLeavesOthersUndisturbed : Whole_Obl_satisfiable_1_everyStepLeavesOthersUndisturbed.
Proof.
  unfold Whole_Obl_satisfiable_1_everyStepLeavesOthersUndisturbed.
  exists settled. exists "p1"%string. exists again. exists (fun _ => None). exists (settled, settled).
  unfold settled, again.
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_2_everyStepLeavesOthersUndisturbed : Whole_Obl_satisfiable_2_everyStepLeavesOthersUndisturbed.
Proof.
  unfold Whole_Obl_satisfiable_2_everyStepLeavesOthersUndisturbed.
  exists settled. exists "p1"%string. exists again. exists (fun _ => None). exists (settled, settled).
  unfold settled, again.
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_2_neverCommitsAhead : Whole_Obl_satisfiable_2_neverCommitsAhead.
Proof.
  unfold Whole_Obl_satisfiable_2_neverCommitsAhead.
  exists settled. exists again. exists (fun _ => None). exists (settled, settled).
  unfold settled, again.
  frflow_evaluate.
Qed.

Lemma Whole_Proofs_satisfiable_3_neverCommitsAhead : Whole_Obl_satisfiable_3_neverCommitsAhead.
Proof.
  unfold Whole_Obl_satisfiable_3_neverCommitsAhead.
  exists settled. exists again. exists (fun _ => None). exists (settled, settled).
  unfold settled, again.
  frflow_evaluate.
Qed.
