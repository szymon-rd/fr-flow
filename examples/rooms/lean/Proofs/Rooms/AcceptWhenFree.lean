import FrFlowGen.Rooms.AcceptWhenFree.Spec

/-! The root over `accepted` and `booked`, from what each is in the code: a request is accepted exactly when
booking it answers booked, which it does exactly when the table holds nothing it overlaps; and what is booked is what
the table holds. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Rooms.AcceptWhenFree.Proofs
open Rooms.AcceptWhenFree

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro booked accepted granted h_BookedIsStored h_AcceptedIsAnswered h_AnswerWhenFree request now hRequest hHeld hApart
  have hAccepted := h_AcceptedIsAnswered request now hRequest hHeld hApart
  have hAnswer := h_AnswerWhenFree request now hRequest hHeld hApart
  have hBooked := h_BookedIsStored now hHeld hApart
  simp only [post, Rooms.AnswerWhenFree.post, Rooms.BookedIsStored.post] at *
  rw [hAccepted, hBooked]
  exact hAnswer

end Rooms.AcceptWhenFree.Proofs
