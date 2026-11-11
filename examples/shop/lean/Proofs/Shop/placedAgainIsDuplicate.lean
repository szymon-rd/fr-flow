import FrFlowGen.Shop.placedAgainIsDuplicate.Spec
import Proofs.Shop.Lemmas

/-! The first call left the order registered (`Lemmas.placed_is_registered`), so the second call's registration is
lost and it answers a duplicate (`Lemmas.lost_place`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.placedAgainIsDuplicate.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro register reserve settle charge release hwon hstays hsettle shop o _
  have marked := placed_is_registered register reserve settle charge release hstays hsettle shop o
  have lost : ¬(register (placeCode register reserve settle charge release shop o).2.journal o.id_).1 :=
    fun won => ((hwon _ o.id_).mp won) marked
  rw [lost_place register reserve settle charge release _ o lost]

end Shop.placedAgainIsDuplicate.Proofs
