import FrFlow

set_option autoImplicit false

set_option linter.unusedVariables false

noncomputable section

open Classical

namespace Rooms

structure Booking where
  room : String
  start : Int
  «end» : Int
deriving DecidableEq

structure RoomBookings where
  bookings : (List Booking)
deriving DecidableEq

@[frflow_defs] def endsAfterStart (b : Booking) : Prop := (b.start < b.«end»)

@[frflow_defs] def covers (b : Booking) (t : Int) : Prop := ((b.start ≤ t) ∧ (t < b.«end»))

@[frflow_defs] def apart (a : Booking) (b : Booking) : Prop := ((¬(a.room = b.room)) ∨ (∀ (t : Int), (¬((Rooms.covers a t) ∧ (Rooms.covers b t)))))

@[frflow_defs] def isFree (held : (List Booking)) (request : Booking) : Prop := (∀ b ∈ held, (Rooms.apart b request))

@[frflow_defs] def noOverlap (a : Booking) (b : Booking) : Prop := (((¬(a.room = b.room)) ∨ (a.«end» ≤ b.start)) ∨ (b.«end» ≤ a.start))

@[frflow_defs] def neverOverlap (held : (List Booking)) : Prop := (List.Pairwise (fun (a : Booking) (b : Booking) => (Rooms.apart a b)) held)

@[frflow_defs] def roomBookingsApart (r : RoomBookings) : Prop := (List.Pairwise (fun (a : Booking) (b : Booking) => (Rooms.noOverlap a b)) r.bookings)

@[frflow_defs] def startsEmpty (held : (List Booking)) : Prop := (held = [])

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

namespace Stored

@[frflow_defs] def inRoom_of (room : String) (s : (List Booking)) : RoomBookings :=
  Id.run ((Stored.inRoom room).run' s)

end Stored

@[frflow_defs] def bookIfGranted {m : Type → Type} [Monad m] [Bookings m] (granted : RoomBookings → Booking → Prop) : Booking → m Prop :=
  fun (request : Booking) => do
    let r ← do
      let r_1 ← Bookings.inRoom request.room
      if (granted r_1 request) then
        Bookings.add request
        pure ()
      else
        pure ()
      pure (granted r_1 request)
    pure r

@[frflow_defs] def bookIfGranted_run (granted : RoomBookings → Booking → Prop) : Booking → World → (Prop × World) :=
  fun (request : Booking) (w : World) => (FrFlow.runOn ((Rooms.bookIfGranted granted) request) w)

namespace grantWhenNoOverlap
@[frflow_defs] def claim (granted : RoomBookings → Booking → Prop) : Prop := (∀ (held : RoomBookings), ((∀ b ∈ held.bookings, (Rooms.endsAfterStart b)) → ((Rooms.roomBookingsApart held) → (∀ (request : Booking), ((Rooms.endsAfterStart request) → ((granted held request) = (∀ b ∈ held.bookings, (Rooms.noOverlap b request))))))))
end grantWhenNoOverlap

namespace grantWhenFree
@[frflow_defs] def claim (granted : RoomBookings → Booking → Prop) : Prop := (∀ (held : RoomBookings), ((∀ b ∈ held.bookings, (Rooms.endsAfterStart b)) → ((Rooms.roomBookingsApart held) → (∀ (request : Booking), ((Rooms.endsAfterStart request) → ((granted held request) = (Rooms.isFree held.bookings request)))))))
end grantWhenFree

namespace bookWhenFree
@[frflow_defs] def claim (book : Booking → (World → (Prop × World))) : Prop := (∀ (request : Booking), ((Rooms.endsAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.store) → ((∀ b ∈ before.store, (Rooms.endsAfterStart b)) → (match (book request before) with | (result, after) => (after.store = (if (Rooms.isFree before.store request) then (before.store ++ [request]) else before.store))))))))
end bookWhenFree

namespace answersWhetherBooked
@[frflow_defs] def claim (book : Booking → (World → (Prop × World))) : Prop := (∀ (request : Booking), ((Rooms.endsAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.store) → ((∀ b ∈ before.store, (Rooms.endsAfterStart b)) → (match (book request before) with | (booked, after) => (booked = (¬(after.store = before.store)))))))))
end answersWhetherBooked

end Rooms

namespace Rooms.neverOverlap

@[frflow_defs] def keeps_book (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.endsAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.store) → ((∀ b ∈ before.store, (Rooms.endsAfterStart b)) → (match (book request before) with | (result, after) => (Rooms.neverOverlap after.store)))))))

end Rooms.neverOverlap

namespace Rooms.endsAfterStart

@[frflow_defs] def keeps_book (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.endsAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.store) → ((∀ b ∈ before.store, (Rooms.endsAfterStart b)) → (match (book request before) with | (result, after) => (∀ b ∈ after.store, (Rooms.endsAfterStart b))))))))

end Rooms.endsAfterStart

namespace Rooms.roomBookingsApart

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.store) → ((∀ b ∈ w.store, (Rooms.endsAfterStart b)) → (Rooms.roomBookingsApart (inRoom room w.store))))))

end Rooms.roomBookingsApart

namespace Rooms.endsAfterStart

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.store) → ((∀ b ∈ w.store, (Rooms.endsAfterStart b)) → (∀ b ∈ (inRoom room w.store).bookings, (Rooms.endsAfterStart b))))))

end Rooms.endsAfterStart

namespace Rooms

namespace bookWhenFree

namespace Obl

/-- Every result of bookIfGranted_run meets bookWhenFree, given what grantWhenFree promise. -/
@[frflow_defs] def impl : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)), (Rooms.bookWhenFree.claim (Rooms.bookIfGranted_run granted))

end Obl

end bookWhenFree

namespace answersWhetherBooked

namespace Obl

/-- Every result of bookIfGranted_run meets answersWhetherBooked, given what grantWhenFree, grantWhenNoOverlap promise. -/
@[frflow_defs] def impl : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)) (h_grantWhenNoOverlap : (Rooms.grantWhenNoOverlap.claim granted)), (Rooms.answersWhetherBooked.claim (Rooms.bookIfGranted_run granted))

end Obl

end answersWhetherBooked

namespace neverOverlap

namespace Obl

/-- Every run of bookIfGranted_run keeps neverOverlap, given what grantWhenFree, grantWhenNoOverlap promise. -/
@[frflow_defs] def cover_book : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)) (h_grantWhenNoOverlap : (Rooms.grantWhenNoOverlap.claim granted)), (Rooms.neverOverlap.keeps_book (Rooms.bookIfGranted_run granted))

end Obl

end neverOverlap

namespace endsAfterStart

namespace Obl

/-- Every run of bookIfGranted_run keeps endsAfterStart, given what grantWhenFree, grantWhenNoOverlap promise. -/
@[frflow_defs] def cover_book : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)) (h_grantWhenNoOverlap : (Rooms.grantWhenNoOverlap.claim granted)), (Rooms.endsAfterStart.keeps_book (Rooms.bookIfGranted_run granted))

end Obl

end endsAfterStart

namespace roomBookingsApart

namespace Obl

/-- Every result of stored's inRoom meets roomBookingsApart, on a world meeting what always holds. -/
@[frflow_defs] def made_inRoom : Prop :=
  (Rooms.roomBookingsApart.makes_inRoom Rooms.Stored.inRoom_of)

end Obl

end roomBookingsApart

namespace endsAfterStart

namespace Obl

/-- Every result of stored's inRoom meets endsAfterStart, on a world meeting what always holds. -/
@[frflow_defs] def made_inRoom : Prop :=
  (Rooms.endsAfterStart.makes_inRoom Rooms.Stored.inRoom_of)

end Obl

end endsAfterStart

namespace Whole

namespace Obl

/-- grantWhenNoOverlap hold together: some meaning of granted makes each true. -/
@[frflow_defs] def consistent_0 : Prop :=
  ∃ (granted : RoomBookings → Booking → Prop), (Rooms.grantWhenNoOverlap.claim granted)

end Obl

namespace Obl

/-- Every state stored may start in meets neverOverlap. -/
@[frflow_defs] def start_neverOverlap : Prop :=
  ∀ (s : (List Booking)), (Rooms.startsEmpty s) → (Rooms.neverOverlap s)

end Obl

namespace Obl

/-- Every state stored may start in meets endsAfterStart. -/
@[frflow_defs] def start_endsAfterStart : Prop :=
  ∀ (s : (List Booking)), (Rooms.startsEmpty s) → ∀ x ∈ s, (Rooms.endsAfterStart x)

end Obl

namespace Obl

/-- Some value meets endsAfterStart. -/
@[frflow_defs] def inhabited_endsAfterStart : Prop :=
  ∃ (x : Booking), (Rooms.endsAfterStart x)

end Obl

namespace Obl

/-- Some value meets roomBookingsApart. -/
@[frflow_defs] def inhabited_roomBookingsApart : Prop :=
  ∃ (x : RoomBookings), (Rooms.roomBookingsApart x)

end Obl

namespace Obl

/-- back to back: granted: what the claims say gives it. -/
@[frflow_defs] def example_0 : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), (Rooms.grantWhenFree.claim granted) → (Rooms.grantWhenNoOverlap.claim granted) → (granted (RoomBookings.mk [(Booking.mk "Oak" 9 10)]) (Booking.mk "Oak" 10 11))

end Obl

namespace Obl

/-- overlapping: not granted: what the claims say gives it. -/
@[frflow_defs] def example_1 : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), (Rooms.grantWhenFree.claim granted) → (Rooms.grantWhenNoOverlap.claim granted) → (¬(granted (RoomBookings.mk [(Booking.mk "Oak" 9 11)]) (Booking.mk "Oak" 10 12)))

end Obl

namespace Obl

/-- another room: granted: what the claims say gives it. -/
@[frflow_defs] def example_2 : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), (Rooms.grantWhenFree.claim granted) → (Rooms.grantWhenNoOverlap.claim granted) → (granted (RoomBookings.mk [(Booking.mk "Elm" 9 11)]) (Booking.mk "Oak" 10 12))

end Obl

theorem consistent_0 : Obl.consistent_0 :=
  ⟨(fun (held : RoomBookings) => (fun (request : Booking) => (∀ b ∈ held.bookings, (Rooms.noOverlap b request)))), by frflow_witness⟩

theorem start_neverOverlap : Obl.start_neverOverlap := by
  frflow_auto

theorem start_endsAfterStart : Obl.start_endsAfterStart := by
  frflow_auto

theorem inhabited_endsAfterStart : Obl.inhabited_endsAfterStart :=
  ⟨(Booking.mk "" 0 1), by frflow_witness⟩

theorem inhabited_roomBookingsApart : Obl.inhabited_roomBookingsApart :=
  ⟨(RoomBookings.mk []), by frflow_witness⟩

end Whole

end Rooms
