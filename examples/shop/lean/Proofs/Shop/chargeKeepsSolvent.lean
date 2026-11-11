import FrFlowGen.Shop.chargeKeepsSolvent.Spec
import Proofs.Shop.Lemmas

/-! A covered charge keeps the books solvent: the customer is left what the amount was covered by, the shop gains
(`Lemmas.charged_solvent`); a charge not made changes nothing. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.chargeKeepsSolvent.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro books o hpos h
  unfold chargeIfCoveredCode
  by_cases hc : o.amount ≤ balance books.postings o.customer
  · simp only [hc, ite_true]
    exact charged_solvent books _ o hpos.2 h hc rfl
  · simp only [hc, ite_false]
    exact h

end Shop.chargeKeepsSolvent.Proofs
