import FrFlowGen.Payments.Whole.Spec

/-! The conditions of the payment stream's claims FrFlow's search found no values for, each shown to hold. Of the
services alone: card limits with a limit of 100 and nothing decided have every card within its limit, and a
ledger in which the payment `p1` is marked has it posted. Of the handler: one in which `p1`, of 30 on a card
with a limit of 100, is decided, approved and marked as posted, handling `p1` again while no other call does
anything; its first step starts from that handler and leaves it as it was.

And the stream's examples FrFlow's automation does not decide within an example's budget, each the run of the code
read from the classes on the states the example gives. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Payments.Whole.Proofs
open Payments

theorem satisfiable_1_authoriseKeepsWithinLimit : Obl.satisfiable_1_authoriseKeepsWithinLimit :=
  ⟨CardLimits.mk 100 [], "card", 1, Payment.mk 0 "p1" "card" "shop" 30 1, by
    simp [recordedLimits_spent, recordedLimits_dailyLimit]⟩

theorem satisfiable_1_postKeepsPosted : Obl.satisfiable_1_postKeepsPosted :=
  ⟨Ledger.mk [] ["p1"], "p1", Payment.mk 0 "p1" "card" "shop" 30 1, by simp [postingLedger_posted]⟩

theorem satisfiable_1_appliedStaysApplied : Obl.satisfiable_1_appliedStaysApplied :=
  ⟨(PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
    "p1", (Payment.mk 0 "p1" "card" "shop" 30 1), by
    simp [streamPaymentHandler_handle_among, recordedLimits_authorise, recordedLimits_decided, recordedLimits_approved,
      recordedLimits_spent, recordedLimits_dailyLimit, postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
      committedOffset_commit, committedOffset_committed, streamPaymentHandler_limits_held,
      streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]⟩

theorem satisfiable_1_everyStepKeepsWithinLimit : Obl.satisfiable_1_everyStepKeepsWithinLimit :=
  ⟨(PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
    "card", 1, (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
      (PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0))), by
    simp [streamPaymentHandler_handle_among, recordedLimits_authorise, recordedLimits_decided, recordedLimits_approved,
      recordedLimits_spent, recordedLimits_dailyLimit, postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
      committedOffset_commit, committedOffset_committed, streamPaymentHandler_limits_held,
      streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]⟩

theorem satisfiable_1_noStepPostsTwice : Obl.satisfiable_1_noStepPostsTwice :=
  ⟨(PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
    "p1", (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
      (PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0))), by
    simp [streamPaymentHandler_handle_among, recordedLimits_authorise, recordedLimits_decided, recordedLimits_approved,
      recordedLimits_spent, recordedLimits_dailyLimit, postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
      committedOffset_commit, committedOffset_committed, streamPaymentHandler_limits_held,
      streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]⟩

theorem satisfiable_1_everyStepLeavesOthersUndisturbed : Obl.satisfiable_1_everyStepLeavesOthersUndisturbed :=
  ⟨(PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
    "p1", (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
      (PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0))), by
    simp [streamPaymentHandler_handle_among, recordedLimits_authorise, recordedLimits_decided, recordedLimits_approved,
      recordedLimits_spent, recordedLimits_dailyLimit, postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
      committedOffset_commit, committedOffset_committed, streamPaymentHandler_limits_held,
      streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]⟩

theorem satisfiable_2_everyStepLeavesOthersUndisturbed : Obl.satisfiable_2_everyStepLeavesOthersUndisturbed :=
  ⟨(PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
    "p1", (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
      (PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0))), by
    simp [streamPaymentHandler_handle_among, recordedLimits_authorise, recordedLimits_decided, recordedLimits_approved,
      recordedLimits_spent, recordedLimits_dailyLimit, postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
      committedOffset_commit, committedOffset_committed, streamPaymentHandler_limits_held,
      streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]⟩

theorem satisfiable_2_neverCommitsAhead : Obl.satisfiable_2_neverCommitsAhead :=
  ⟨(PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
    (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
      (PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0))), by
    simp [streamPaymentHandler_handle_among, recordedLimits_authorise, recordedLimits_decided, recordedLimits_approved,
      recordedLimits_spent, recordedLimits_dailyLimit, postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
      committedOffset_commit, committedOffset_committed, streamPaymentHandler_limits_held,
      streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]⟩

theorem satisfiable_3_neverCommitsAhead : Obl.satisfiable_3_neverCommitsAhead :=
  ⟨(PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
    (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0)),
      (PaymentHandler.mk (CardLimits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Ledger.mk [] ["p1"]) (ConsumerOffsets.mk 0))), by
    simp [streamPaymentHandler_handle_among, recordedLimits_authorise, recordedLimits_decided, recordedLimits_approved,
      recordedLimits_spent, recordedLimits_dailyLimit, postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
      committedOffset_commit, committedOffset_committed, streamPaymentHandler_limits_held,
      streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]⟩

theorem example_PaymentsExamples_0 : Obl.example_PaymentsExamples_0 := by
  unfold Obl.example_PaymentsExamples_0
  intros
  simp [postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
    postingLedger_total, committedOffset_commit, committedOffset_committed,
    recordedLimits_approved, recordedLimits_authorise, recordedLimits_decided,
    recordedLimits_dailyLimit, recordedLimits_spent, streamPaymentHandler_handle, streamPaymentHandler_handle_among,
    streamPaymentHandler_limits_held, streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]

theorem example_PaymentsExamples_1 : Obl.example_PaymentsExamples_1 := by
  unfold Obl.example_PaymentsExamples_1
  intros
  simp [postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
    postingLedger_total, committedOffset_commit, committedOffset_committed,
    recordedLimits_approved, recordedLimits_authorise, recordedLimits_decided,
    recordedLimits_dailyLimit, recordedLimits_spent, streamPaymentHandler_handle, streamPaymentHandler_handle_among,
    streamPaymentHandler_limits_held, streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]

theorem example_PaymentsExamples_2 : Obl.example_PaymentsExamples_2 := by
  unfold Obl.example_PaymentsExamples_2
  intros
  simp [postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
    postingLedger_total, committedOffset_commit, committedOffset_committed,
    recordedLimits_approved, recordedLimits_authorise, recordedLimits_decided,
    recordedLimits_dailyLimit, recordedLimits_spent, streamPaymentHandler_handle, streamPaymentHandler_handle_among,
    streamPaymentHandler_limits_held, streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]

theorem example_PaymentsExamples_3 : Obl.example_PaymentsExamples_3 := by
  unfold Obl.example_PaymentsExamples_3
  intros
  simp [postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
    postingLedger_total, committedOffset_commit, committedOffset_committed,
    recordedLimits_approved, recordedLimits_authorise, recordedLimits_decided,
    recordedLimits_dailyLimit, recordedLimits_spent, streamPaymentHandler_handle, streamPaymentHandler_handle_among,
    streamPaymentHandler_limits_held, streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]

theorem example_PaymentsExamples_4 : Obl.example_PaymentsExamples_4 := by
  unfold Obl.example_PaymentsExamples_4
  intros
  rename_i step taken
  revert step taken
  simp [postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
    postingLedger_total, committedOffset_commit, committedOffset_committed,
    recordedLimits_approved, recordedLimits_authorise, recordedLimits_decided,
    recordedLimits_dailyLimit, recordedLimits_spent, streamPaymentHandler_handle, streamPaymentHandler_handle_among,
    streamPaymentHandler_limits_held, streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]

theorem example_PaymentsExamples_5 : Obl.example_PaymentsExamples_5 := by
  unfold Obl.example_PaymentsExamples_5
  intros
  simp [commitFirstHandler_handle_among, commitFirstHandler_limits_held,
    commitFirstHandler_ledger_held, commitFirstHandler_offsets_held, postingLedger_post, postingLedger_posted,
    postingLedger_postingsOf, postingLedger_total, committedOffset_commit, committedOffset_committed,
    recordedLimits_approved, recordedLimits_authorise, recordedLimits_decided,
    recordedLimits_dailyLimit, recordedLimits_spent]

theorem example_PaymentsExamples_6 : Obl.example_PaymentsExamples_6 := by
  unfold Obl.example_PaymentsExamples_6
  intros
  simp [checkThenActHandler_handle, checkThenActHandler_handle_among, checkThenActHandler_limits_held,
    checkThenActHandler_ledger_held, postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
    postingLedger_total, committedOffset_commit, committedOffset_committed,
    recordedLimits_approved, recordedLimits_authorise, recordedLimits_decided,
    recordedLimits_dailyLimit, recordedLimits_spent]

theorem example_PaymentsExamples_7 : Obl.example_PaymentsExamples_7 := by
  unfold Obl.example_PaymentsExamples_7
  intros
  simp [postingLedger_post, postingLedger_posted, postingLedger_postingsOf,
    postingLedger_total, committedOffset_commit, committedOffset_committed,
    recordedLimits_approved, recordedLimits_authorise, recordedLimits_decided,
    recordedLimits_dailyLimit, recordedLimits_spent, streamPaymentHandler_handle, streamPaymentHandler_handle_among,
    streamPaymentHandler_limits_held, streamPaymentHandler_ledger_held, streamPaymentHandler_offsets_held]

end Payments.Whole.Proofs
