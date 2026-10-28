import FrFlowGen.Rooms.grantWhenFree.Spec
import Proofs.Rooms.Lemmas

/-! The claim over moments, from the claim over start and end times: two bookings that end after they start are
apart exactly when they do not overlap (if they share a room and neither ends before the other starts, the later
start is a moment both cover), so the two claims give `granted` the same answer. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Rooms.grantWhenFree.Proofs

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro granted h
  unfold claim
  intro held hRoom hApart hEnds request hRequest
  rw [h held hRoom hApart hEnds request hRequest]
  simp only [free]
  exact propext (forall₂_congr fun b hb => (Lemmas.apart_iff_noOverlap (hEnds b hb) hRequest).symm)

end Rooms.grantWhenFree.Proofs
