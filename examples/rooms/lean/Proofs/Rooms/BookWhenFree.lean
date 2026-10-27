import FrFlowGen.Rooms.BookWhenFree.Spec

/-! The root over `bookedAfter` and `booked`, from what each is in the code's words: what is booked once a request is
handled is what the table holds after booking the request that asks for it, which holds its booking added exactly
when the table held nothing it overlaps; and what is booked is what the table holds. The request asking for a booking
asks for that booking. -/

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
  have hStored := h_StoreWhenFree (Rooms.asRequest request) now hRequest hHeld hApart
  have hBooked := h_BookedIsStored now hHeld hApart
  simp only [post, Rooms.BookedAfterIsStored.post, Rooms.StoreWhenFree.post, Rooms.BookedIsStored.post] at *
  rw [hAfter, hBooked]
  exact hStored

end Rooms.BookWhenFree.Proofs
