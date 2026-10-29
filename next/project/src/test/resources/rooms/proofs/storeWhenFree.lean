import FrFlowGen.Rooms.storeWhenFree.Spec
import Proofs.Rooms.Lemmas

/-! What booking stores, of its program: the run's equation, then cases on the calendar's answer, which the
calendar's claim gives as the store's being free. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Rooms.storeWhenFree.Proofs

theorem impl : Obl.impl := by
  intro granted h request hr before hno hv
  rw [Lemmas.run_eq]
  have hg := Lemmas.granted_free granted h request hr before.storedBookings hno hv
  by_cases hf : free before.storedBookings request
  · have hy : granted ⟨request.room, before.storedBookings.filter (fun b => decide (b.room = request.room))⟩ request :=
      hg ▸ hf
    simp [hy, hf]
  · have hn : ¬granted ⟨request.room, before.storedBookings.filter (fun b => decide (b.room = request.room))⟩ request :=
      hg ▸ hf
    simp [hn, hf]

end Rooms.storeWhenFree.Proofs
