import FrFlowGen.Rooms.roomBookingsApart.Spec
import Proofs.Rooms.Lemmas

/-! The table's `inRoom` gives a room's bookings that never overlap, from a store whose bookings never overlap and
end after they start: what the calendar is given meets its rule. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Rooms.roomBookingsApart.Proofs

theorem made_inRoom : Obl.made_inRoom := by
  intro room w hno hv
  have : StoredBookings.inRoom_of room w.storedBookings =
      ⟨room, w.storedBookings.filter (fun b => decide (b.room = room))⟩ := by
    simp [StoredBookings.inRoom_of, StoredBookings.inRoom]
  rw [this]
  exact Lemmas.room_apart w.storedBookings room hno hv

end Rooms.roomBookingsApart.Proofs
