import FrFlowGen.Shop.refusedLeavesNothing.Spec
import Proofs.Shop.Lemmas

/-! The compensation. Out of stock: the reservation was not made, so the stock is as it was, and the books were not
touched. Payment refused: the units reserved were released, which leaves every product with what it had; the charge
was not done, so it made no posting. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.refusedLeavesNothing.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro register reserve settle charge release hrefused hundoes hfailed shop sku o hpos hout
  unfold placeCode at hout ⊢
  by_cases hmine : (register shop.journal o.id_).1
  · by_cases hres : (reserve shop.stock o).1
    · by_cases hch : (charge shop.books o).1 = Charged.Done
      · simp [hmine, hres, hch] at hout
      · simp only [hmine, hres, hch, not_true_eq_false, ite_false]
        exact ⟨hundoes shop.stock sku o hpos hres, hfailed shop.books o hpos hch⟩
    · simp only [hmine, hres, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
      simp [hrefused shop.stock o hpos hres]
  · simp [hmine] at hout

end Shop.refusedLeavesNothing.Proofs
