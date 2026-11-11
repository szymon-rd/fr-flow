import FrFlowGen.Shop.placedAgainChangesNothing.Spec
import Proofs.Shop.Lemmas

/-! The first call left the order registered, so the second call's registration is lost; a lost registration leaves
the journal as it is, and the call does nothing else. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Shop.placedAgainChangesNothing.Proofs
open Shop Shop.Lemmas

theorem impl : Obl.impl := by
  intro register reserve settle charge release hwon hstays hlost hsettle shop o _
  have marked := placed_is_registered register reserve settle charge release hstays hsettle shop o
  have lost : ¬(register (placeCode register reserve settle charge release shop o).2.journal o.id_).1 :=
    fun won => ((hwon _ o.id_).mp won) marked
  rw [lost_place register reserve settle charge release _ o lost]
  simp only [hlost _ o.id_ lost]

end Shop.placedAgainChangesNothing.Proofs
