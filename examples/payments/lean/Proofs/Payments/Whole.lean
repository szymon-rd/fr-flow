import FrFlowGen.Payments.Whole.Spec

/-! The conditions of the payment stream's claims FrFlow's search found no values for, each shown to hold. Of the
services alone: a limits service with a limit of 100 and nothing decided has every card within its limit, and
accounts in which the payment `p1` is marked have it posted. Of the processor: one in which `p1`, of 30 on a card
with a limit of 100, is decided, approved and marked as posted, handling `p1` again while no other call does
anything; its first step starts from that processor and leaves it as it was. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Payments.Whole.Proofs
open Payments

theorem satisfiable_1_authoriseKeepsWithinLimit : Obl.satisfiable_1_authoriseKeepsWithinLimit :=
  ⟨Limits.mk 100 [], "card", 1, Payment.mk 0 "p1" "card" "shop" 30 1, by
    simp [spendLimits_spent, spendLimits_limit]⟩

theorem satisfiable_1_postKeepsPosted : Obl.satisfiable_1_postKeepsPosted :=
  ⟨Accounts.mk [] ["p1"], "p1", Payment.mk 0 "p1" "card" "shop" 30 1, by simp [ledgerAccounts_posted]⟩

theorem satisfiable_1_appliedStaysApplied : Obl.satisfiable_1_appliedStaysApplied :=
  ⟨(Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
    "p1", (Payment.mk 0 "p1" "card" "shop" 30 1), by
    simp [streamProcessor_handle_among, spendLimits_authorise, spendLimits_decided, spendLimits_approved,
      spendLimits_spent, spendLimits_limit, ledgerAccounts_post, ledgerAccounts_posted, ledgerAccounts_postingsOf,
      offsetCheckpoint_commit, streamProcessor_spent, streamProcessor_limit, streamProcessor_postingsOf,
      streamProcessor_posted, streamProcessor_decided, streamProcessor_approved, streamProcessor_applied]⟩

theorem satisfiable_1_everyStepKeepsWithinLimit : Obl.satisfiable_1_everyStepKeepsWithinLimit :=
  ⟨(Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
    "card", 1, (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
      (Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0))), by
    simp [streamProcessor_handle_among, spendLimits_authorise, spendLimits_decided, spendLimits_approved,
      spendLimits_spent, spendLimits_limit, ledgerAccounts_post, ledgerAccounts_posted, ledgerAccounts_postingsOf,
      offsetCheckpoint_commit, streamProcessor_spent, streamProcessor_limit, streamProcessor_postingsOf,
      streamProcessor_posted, streamProcessor_decided, streamProcessor_approved, streamProcessor_applied]⟩

theorem satisfiable_1_noStepPostsTwice : Obl.satisfiable_1_noStepPostsTwice :=
  ⟨(Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
    "p1", (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
      (Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0))), by
    simp [streamProcessor_handle_among, spendLimits_authorise, spendLimits_decided, spendLimits_approved,
      spendLimits_spent, spendLimits_limit, ledgerAccounts_post, ledgerAccounts_posted, ledgerAccounts_postingsOf,
      offsetCheckpoint_commit, streamProcessor_spent, streamProcessor_limit, streamProcessor_postingsOf,
      streamProcessor_posted, streamProcessor_decided, streamProcessor_approved, streamProcessor_applied]⟩

theorem satisfiable_1_everyStepLeavesOthersUndisturbed : Obl.satisfiable_1_everyStepLeavesOthersUndisturbed :=
  ⟨(Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
    "p1", (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
      (Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0))), by
    simp [streamProcessor_handle_among, spendLimits_authorise, spendLimits_decided, spendLimits_approved,
      spendLimits_spent, spendLimits_limit, ledgerAccounts_post, ledgerAccounts_posted, ledgerAccounts_postingsOf,
      offsetCheckpoint_commit, streamProcessor_spent, streamProcessor_limit, streamProcessor_postingsOf,
      streamProcessor_posted, streamProcessor_decided, streamProcessor_approved, streamProcessor_applied]⟩

theorem satisfiable_2_everyStepLeavesOthersUndisturbed : Obl.satisfiable_2_everyStepLeavesOthersUndisturbed :=
  ⟨(Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
    "p1", (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
      (Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0))), by
    simp [streamProcessor_handle_among, spendLimits_authorise, spendLimits_decided, spendLimits_approved,
      spendLimits_spent, spendLimits_limit, ledgerAccounts_post, ledgerAccounts_posted, ledgerAccounts_postingsOf,
      offsetCheckpoint_commit, streamProcessor_spent, streamProcessor_limit, streamProcessor_postingsOf,
      streamProcessor_posted, streamProcessor_decided, streamProcessor_approved, streamProcessor_applied]⟩

theorem satisfiable_2_neverCommitsAhead : Obl.satisfiable_2_neverCommitsAhead :=
  ⟨(Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
    (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
      (Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0))), by
    simp [streamProcessor_handle_among, spendLimits_authorise, spendLimits_decided, spendLimits_approved,
      spendLimits_spent, spendLimits_limit, ledgerAccounts_post, ledgerAccounts_posted, ledgerAccounts_postingsOf,
      offsetCheckpoint_commit, streamProcessor_spent, streamProcessor_limit, streamProcessor_postingsOf,
      streamProcessor_posted, streamProcessor_decided, streamProcessor_approved, streamProcessor_applied]⟩

theorem satisfiable_3_neverCommitsAhead : Obl.satisfiable_3_neverCommitsAhead :=
  ⟨(Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
    (Payment.mk 0 "p1" "card" "shop" 30 1), (fun _ => none),
    ((Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0)),
      (Processor.mk (Limits.mk 100 [Decision.mk "p1" "card" 1 30 True]) (Accounts.mk [] ["p1"]) (Checkpoint.mk 0))), by
    simp [streamProcessor_handle_among, spendLimits_authorise, spendLimits_decided, spendLimits_approved,
      spendLimits_spent, spendLimits_limit, ledgerAccounts_post, ledgerAccounts_posted, ledgerAccounts_postingsOf,
      offsetCheckpoint_commit, streamProcessor_spent, streamProcessor_limit, streamProcessor_postingsOf,
      streamProcessor_posted, streamProcessor_decided, streamProcessor_approved, streamProcessor_applied]⟩

end Payments.Whole.Proofs
