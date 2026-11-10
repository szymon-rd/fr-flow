import FrFlowGen.Wallet.hastyIsSafeAlone.Spec
import Proofs.Wallet.Lemmas

/-! Alone, the hasty transfer keeps the books solvent: with no other call between its steps, the balance it read
is the balance it moves from (`Lemmas.moved_solvent`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Wallet.hastyIsSafeAlone.Proofs
open Wallet Wallet.Lemmas

theorem impl : Obl.impl := by
  intro books t hpos h
  unfold hastyCode
  by_cases hseen : t.request ∈ books.claimed
  · simp only [hseen, ite_true]
    exact h
  · by_cases hc : t.amount ≤ balance books.postings t.«from»
    · simp only [hseen, hc, ite_true, ite_false]
      exact moved_solvent books _ t hpos h hc rfl
    · simp only [hseen, hc, ite_false]
      exact same_postings_solvent books _ h rfl

end Wallet.hastyIsSafeAlone.Proofs
