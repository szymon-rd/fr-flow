/-- The boundary store: the SQLite table the bookings are kept in -/
class Bookings (m : Type → Type) where
  inRoom : String → m RoomBookings
  add : Booking → m Unit

namespace Stored

@[frflow_defs] def inRoom : String → StateM (List Booking) RoomBookings :=
  fun (room : String) => do
    let r ← get
    pure (RoomBookings.mk (List.filter (fun b => decide (b.room = room)) r))

@[frflow_defs] def add : Booking → StateM (List Booking) Unit :=
  fun (booking : Booking) => do
    let r ← get
    set (r ++ [booking])
    pure ()

end Stored

/-- The models' states: what proven flows run on. -/
structure World where
  store : (List Booking)

instance : Bookings (StateM World) where
  inRoom room := FrFlow.within (fun w => w.store) (fun w s => { w with store := s }) (Stored.inRoom room)
  add booking := FrFlow.within (fun w => w.store) (fun w s => { w with store := s }) (Stored.add booking)

@[frflow_defs] theorem Bookings.inRoom_onWorld (room : String) :
    ((Bookings.inRoom room) : StateM World RoomBookings) = FrFlow.within (fun w => w.store) (fun w s => { w with store := s }) (Stored.inRoom room) := rfl

@[frflow_defs] theorem Bookings.add_onWorld (booking : Booking) :
    ((Bookings.add booking) : StateM World Unit) = FrFlow.within (fun w => w.store) (fun w s => { w with store := s }) (Stored.add booking) := rfl
