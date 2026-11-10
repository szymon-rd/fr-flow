import FrFlowGen.Wallet.moveKeepsSolvent.Spec
import Proofs.Wallet.Lemmas

/-! Moving money if covered keeps the books solvent: the payer is left what the amount was covered by, the payee
gains (`Lemmas.moved_solvent`); a move not made changes nothing. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Wallet.moveKeepsSolvent.Proofs
open Wallet Wallet.Lemmas

theorem impl : Obl.impl := by
  intro books t hpos h
  unfold moveIfCoveredCode
  by_cases hc : t.amount ≤ balance books.postings t.«from»
  · simp only [hc, ite_true]
    exact moved_solvent books _ t hpos h hc rfl
  · simp only [hc, ite_false]
    exact h

end Wallet.moveKeepsSolvent.Proofs
