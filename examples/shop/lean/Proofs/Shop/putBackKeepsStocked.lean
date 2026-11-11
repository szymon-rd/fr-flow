import FrFlowGen.Shop.putBackKeepsStocked.Spec
import Proofs.Shop.Lemmas

/-! Units put back only add to what a product has to sell (`Lemmas.added_stocked`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.putBackKeepsStocked.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro stock o hpos h
  unfold putBackCode
  exact added_stocked stock _ (Movement.mk o.id_ o.sku o.units) (Int.le_of_lt hpos.1) h rfl

end Shop.putBackKeepsStocked.Proofs
