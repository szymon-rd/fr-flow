import FrFlowGen.Payments.Whole.Spec

/-! The conditions of the payment stream's claims FrFlow's search found no values for, each shown to hold: a limits
service with a limit of 100 and nothing decided has every card within its limit, and accounts in which the payment
`p1` is marked have it posted. -/

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

end Payments.Whole.Proofs
