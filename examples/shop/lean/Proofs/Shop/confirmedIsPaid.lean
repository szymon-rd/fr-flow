import FrFlowGen.Shop.confirmedIsPaid.Spec
import Proofs.Shop.Lemmas

/-! An order is confirmed only when its charge was done, and nothing after the charge touches the books: what the
payments service says of a charge done is what holds of the shop. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.confirmedIsPaid.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro register reserve settle charge release hpays shop account o hpos hconf
  unfold placeCode at hconf ⊢
  by_cases hmine : (register shop.journal o.id_).1
  · by_cases hres : (reserve shop.stock o).1
    · by_cases hch : (charge shop.books o).1 = Charged.Done
      · simp only [hmine, hres, hch, not_true_eq_false, ite_true, ite_false]
        exact hpays shop.books account o hpos hch
      · simp [hmine, hres, hch] at hconf
    · simp [hmine, hres] at hconf
  · simp [hmine] at hconf

end Shop.confirmedIsPaid.Proofs
