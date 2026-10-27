import FrFlowGen.Rooms.BookWhenFree.Spec

/-! The root over `bookedAfter` and `booked`, from what each is in the code: what is booked once a request is
handled is what the table holds after booking it, which holds the request added exactly when the table held nothing
it overlaps; and what is booked is what the table holds. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Rooms.BookWhenFree.Proofs
open Rooms.BookWhenFree

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro booked bookedAfter granted h_BookedIsStored h_BookedAfterIsStored h_StoreWhenFree request now hRequest hHeld
    hApart
  have hAfter := h_BookedAfterIsStored request now hRequest hHeld hApart
  have hStored := h_StoreWhenFree request now hRequest hHeld hApart
  have hBooked := h_BookedIsStored now hHeld hApart
  simp only [post, Rooms.StoreWhenFree.post, Rooms.BookedIsStored.post] at *
  rw [hAfter, hBooked]
  exact hStored

end Rooms.BookWhenFree.Proofs
