import FrFlowGen.Rooms.answerWhenFree.Spec
import Proofs.Rooms.Lemmas

/-! What booking answers, of its program: the run's answer is the calendar's, which the calendar's claim gives as
the store's being free. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Rooms.answerWhenFree.Proofs

theorem impl : Obl.impl := by
  intro granted h request hr before hno hv
  rw [Lemmas.run_eq]
  exact Lemmas.granted_free granted h request hr before.storedBookings hno hv

end Rooms.answerWhenFree.Proofs
