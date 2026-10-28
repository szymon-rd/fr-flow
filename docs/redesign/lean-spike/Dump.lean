-- Rooms as the rebuild's printer gives it (next/, step 11): every generated module but those holding
-- proofs (Auto, Impl, Theorems, Checks, RootImpl), one after another in import order.

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

structure RoomBookings where
  room : String
  bookings : (List Booking)

end Rooms

namespace Rooms

/-- The boundary bookingTable: the SQLite table the bookings are kept in -/
class BookingTable (m : Type → Type) where
  inRoom : String → m RoomBookings
  add : Booking → m Unit

namespace StoredBookings

@[frflow_defs] def inRoom : String → StateM (List Booking) RoomBookings :=
  fun (room : String) => do
    let r ← get
    pure (RoomBookings.mk room (List.filter (fun b => decide (b.room = room)) r))

@[frflow_defs] def add : Booking → StateM (List Booking) Unit :=
  fun (booking : Booking) => do
    let r ← get
    set (r ++ [booking])
    pure ()

end StoredBookings

/-- The models' states: what proven flows run on. -/
structure World where
  bookingTable : (List Booking)

instance : BookingTable (StateM World) where
  inRoom room := FrFlow.within (fun w => w.bookingTable) (fun w s => { w with bookingTable := s }) (StoredBookings.inRoom room)
  add booking := FrFlow.within (fun w => w.bookingTable) (fun w s => { w with bookingTable := s }) (StoredBookings.add booking)

@[frflow_defs] theorem BookingTable.inRoom_onWorld (room : String) :
    ((BookingTable.inRoom room) : StateM World RoomBookings) = FrFlow.within (fun w => w.bookingTable) (fun w s => { w with bookingTable := s }) (StoredBookings.inRoom room) := rfl

@[frflow_defs] theorem BookingTable.add_onWorld (booking : Booking) :
    ((BookingTable.add booking) : StateM World Unit) = FrFlow.within (fun w => w.bookingTable) (fun w s => { w with bookingTable := s }) (StoredBookings.add booking) := rfl

namespace StoredBookings

@[frflow_defs] def inRoom_of (room : String) (s : (List Booking)) : RoomBookings :=
  Id.run ((StoredBookings.inRoom room).run' s)

end StoredBookings

end Rooms

namespace Rooms

@[frflow_defs] def noOverlap (a : Booking) (b : Booking) : Prop :=
  (((¬(a.room = b.room)) ∨ (a.«end» ≤ b.start)) ∨ (b.«end» ≤ a.start))

frflow_match_eqns

end Rooms

namespace Rooms

@[frflow_defs] def startsEmpty (stored : (List Booking)) : Prop :=
  (stored = ([] : (List Booking)))

frflow_match_eqns

end Rooms

namespace Rooms

@[frflow_defs] def covers (b : Booking) (t : Int) : Prop :=
  ((b.start ≤ t) ∧ (t < b.«end»))

frflow_match_eqns

end Rooms

namespace Rooms

@[frflow_defs] def apart (a : Booking) (b : Booking) : Prop :=
  ((¬(a.room = b.room)) ∨ (∀ (t : Int), (¬((Rooms.covers a t) ∧ (Rooms.covers b t)))))

frflow_match_eqns

end Rooms

namespace Rooms

@[frflow_defs] def bookIfGranted {m : Type → Type} [Monad m] [BookingTable m] (granted : RoomBookings → Booking → Prop) : Booking → m Prop :=
  fun (request : Booking) => do
    let r ← do
      let r_1 ← BookingTable.inRoom request.room
      if (granted r_1 request) then
        BookingTable.add request
        pure ()
      else
        pure ()
      pure (granted r_1 request)
    pure r

frflow_match_eqns

end Rooms

namespace Rooms

@[frflow_defs] def bookIfGranted_run (granted : RoomBookings → Booking → Prop) : Booking → World → (Prop × World) :=
  fun (request : Booking) (w : World) => (FrFlow.runOn ((Rooms.bookIfGranted granted) request) w)

frflow_match_eqns

end Rooms

namespace Rooms

@[frflow_defs] def bookingsEndAfterStart (b : Booking) : Prop :=
  (b.start < b.«end»)

frflow_match_eqns

end Rooms

namespace Rooms

@[frflow_defs] def roomBookingsApart (held : RoomBookings) : Prop :=
  (List.Pairwise (fun (a : Booking) (b : Booking) => (Rooms.noOverlap a b)) held.bookings)

frflow_match_eqns

end Rooms

namespace Rooms

@[frflow_defs] def free (bookings : (List Booking)) (request : Booking) : Prop :=
  (∀ b ∈ bookings, (Rooms.apart b request))

frflow_match_eqns

end Rooms

namespace Rooms

@[frflow_defs] def neverOverlap (stored : (List Booking)) : Prop :=
  (List.Pairwise (fun (a : Booking) (b : Booking) => (Rooms.apart a b)) stored)

frflow_match_eqns

end Rooms

namespace Rooms

@[frflow_defs] def bookingsOfTheRoom (held : RoomBookings) : Prop :=
  (∀ b ∈ held.bookings, (b.room = held.room))

frflow_match_eqns

end Rooms

namespace Rooms

end Rooms

namespace Rooms.bookedIsStored

@[frflow_defs] def claim (booked : World → (List Booking)) : Prop :=
  (∀ (now : World), ((Rooms.neverOverlap now.bookingTable) → ((∀ b ∈ now.bookingTable, (Rooms.bookingsEndAfterStart b)) → ((booked now) = now.bookingTable))))

namespace Obl

/-- No world meets bookedIsStored. -/
@[frflow_defs] def unsat : Prop :=
  ∀ (booked : World → (List Booking)), ¬ (Rooms.bookedIsStored.claim booked)

end Obl

frflow_match_eqns

end Rooms.bookedIsStored

namespace Rooms.bookedAfterIsStored

@[frflow_defs] def claim (book : Booking → (World → (Prop × World))) (bookedAfter : Booking → World → (List Booking)) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (now : World), ((Rooms.neverOverlap now.bookingTable) → ((∀ b ∈ now.bookingTable, (Rooms.bookingsEndAfterStart b)) → (match (book request now) with | (result, after) => ((bookedAfter request now) = after.bookingTable)))))))

namespace Obl

/-- No world meets bookedAfterIsStored. -/
@[frflow_defs] def unsat : Prop :=
  ∀ (book : Booking → (World → (Prop × World))) (bookedAfter : Booking → World → (List Booking)), ¬ (Rooms.bookedAfterIsStored.claim book bookedAfter)

end Obl

frflow_match_eqns

end Rooms.bookedAfterIsStored

namespace Rooms.grantWhenNoOverlap

@[frflow_defs] def claim (granted : RoomBookings → Booking → Prop) : Prop :=
  (∀ (held : RoomBookings), ((Rooms.bookingsOfTheRoom held) → ((Rooms.roomBookingsApart held) → ((∀ b ∈ held.bookings, (Rooms.bookingsEndAfterStart b)) → (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → ((granted held request) = (∀ b ∈ held.bookings, (Rooms.noOverlap b request)))))))))

namespace Obl

/-- No world meets grantWhenNoOverlap. -/
@[frflow_defs] def unsat : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ¬ (Rooms.grantWhenNoOverlap.claim granted)

end Obl

frflow_match_eqns

end Rooms.grantWhenNoOverlap

namespace Rooms.grantWhenFree

@[frflow_defs] def claim (granted : RoomBookings → Booking → Prop) : Prop :=
  (∀ (held : RoomBookings), ((Rooms.bookingsOfTheRoom held) → ((Rooms.roomBookingsApart held) → ((∀ b ∈ held.bookings, (Rooms.bookingsEndAfterStart b)) → (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → ((granted held request) = (Rooms.free held.bookings request))))))))

namespace Obl

/-- The parts of grantWhenFree (grantWhenNoOverlap) together make it. -/
@[frflow_defs] def complete : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenNoOverlap : (Rooms.grantWhenNoOverlap.claim granted)), (Rooms.grantWhenFree.claim granted)

end Obl

namespace Obl

/-- grantWhenFree holds whatever grantWhenNoOverlap says. -/
@[frflow_defs] def vacuous : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), (Rooms.grantWhenFree.claim granted)

end Obl

namespace Obl

/-- grantWhenNoOverlap follows from grantWhenFree. -/
@[frflow_defs] def restates : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)), (Rooms.grantWhenNoOverlap.claim granted)

end Obl

namespace Obl

/-- The parts of grantWhenFree contradict each other. -/
@[frflow_defs] def clash : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenNoOverlap : (Rooms.grantWhenNoOverlap.claim granted)), False

end Obl

namespace Obl

/-- No world meets grantWhenFree. -/
@[frflow_defs] def unsat : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ¬ (Rooms.grantWhenFree.claim granted)

end Obl

frflow_match_eqns

end Rooms.grantWhenFree

namespace Rooms.storeWhenFree

@[frflow_defs] def claim (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.bookingTable) → ((∀ b ∈ before.bookingTable, (Rooms.bookingsEndAfterStart b)) → (match (book request before) with | (result, after) => (after.bookingTable = (if (Rooms.free before.bookingTable request) then (before.bookingTable ++ [request]) else before.bookingTable))))))))

namespace Obl

/-- Every result of bookIfGranted_run meets storeWhenFree, given what grantWhenFree promise. -/
@[frflow_defs] def impl : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)), (Rooms.storeWhenFree.claim (Rooms.bookIfGranted_run granted))

end Obl

namespace Obl

/-- storeWhenFree holds whatever grantWhenFree says. -/
@[frflow_defs] def vacuous : Prop :=
  ∀ (book : Booking → (World → (Prop × World))) (granted : RoomBookings → Booking → Prop), (Rooms.storeWhenFree.claim book)

end Obl

namespace Obl

/-- grantWhenFree follows from storeWhenFree. -/
@[frflow_defs] def restates : Prop :=
  ∀ (book : Booking → (World → (Prop × World))) (granted : RoomBookings → Booking → Prop), ∀ (h_storeWhenFree : (Rooms.storeWhenFree.claim book)), (Rooms.grantWhenFree.claim granted)

end Obl

namespace Obl

/-- The parts of storeWhenFree contradict each other. -/
@[frflow_defs] def clash : Prop :=
  ∀ (book : Booking → (World → (Prop × World))) (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)), False

end Obl

namespace Obl

/-- No world meets storeWhenFree. -/
@[frflow_defs] def unsat : Prop :=
  ∀ (book : Booking → (World → (Prop × World))), ¬ (Rooms.storeWhenFree.claim book)

end Obl

frflow_match_eqns

end Rooms.storeWhenFree

namespace Rooms.bookWhenFree

@[frflow_defs] def claim (bookedAfter : Booking → World → (List Booking)) (booked : World → (List Booking)) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (now : World), ((Rooms.neverOverlap now.bookingTable) → ((∀ b ∈ now.bookingTable, (Rooms.bookingsEndAfterStart b)) → ((bookedAfter request now) = (if (Rooms.free (booked now) request) then ((booked now) ++ [request]) else (booked now))))))))

namespace Obl

/-- The parts of bookWhenFree (bookedIsStored, bookedAfterIsStored, storeWhenFree) together make it. -/
@[frflow_defs] def complete : Prop :=
  ∀ (bookedAfter : Booking → World → (List Booking)) (booked : World → (List Booking)) (book : Booking → (World → (Prop × World))), ∀ (h_bookedIsStored : (Rooms.bookedIsStored.claim booked)) (h_bookedAfterIsStored : (Rooms.bookedAfterIsStored.claim book bookedAfter)) (h_storeWhenFree : (Rooms.storeWhenFree.claim book)), (Rooms.bookWhenFree.claim bookedAfter booked)

end Obl

namespace Obl

/-- bookWhenFree holds without bookedIsStored. -/
@[frflow_defs] def needed_bookedIsStored : Prop :=
  ∀ (bookedAfter : Booking → World → (List Booking)) (booked : World → (List Booking)) (book : Booking → (World → (Prop × World))), ∀ (h_bookedAfterIsStored : (Rooms.bookedAfterIsStored.claim book bookedAfter)) (h_storeWhenFree : (Rooms.storeWhenFree.claim book)), (Rooms.bookWhenFree.claim bookedAfter booked)

end Obl

namespace Obl

/-- bookWhenFree holds without bookedAfterIsStored. -/
@[frflow_defs] def needed_bookedAfterIsStored : Prop :=
  ∀ (bookedAfter : Booking → World → (List Booking)) (booked : World → (List Booking)) (book : Booking → (World → (Prop × World))), ∀ (h_bookedIsStored : (Rooms.bookedIsStored.claim booked)) (h_storeWhenFree : (Rooms.storeWhenFree.claim book)), (Rooms.bookWhenFree.claim bookedAfter booked)

end Obl

namespace Obl

/-- bookWhenFree holds without storeWhenFree. -/
@[frflow_defs] def needed_storeWhenFree : Prop :=
  ∀ (bookedAfter : Booking → World → (List Booking)) (booked : World → (List Booking)) (book : Booking → (World → (Prop × World))), ∀ (h_bookedIsStored : (Rooms.bookedIsStored.claim booked)) (h_bookedAfterIsStored : (Rooms.bookedAfterIsStored.claim book bookedAfter)), (Rooms.bookWhenFree.claim bookedAfter booked)

end Obl

namespace Obl

/-- The parts of bookWhenFree contradict each other. -/
@[frflow_defs] def clash : Prop :=
  ∀ (bookedAfter : Booking → World → (List Booking)) (booked : World → (List Booking)) (book : Booking → (World → (Prop × World))), ∀ (h_bookedIsStored : (Rooms.bookedIsStored.claim booked)) (h_bookedAfterIsStored : (Rooms.bookedAfterIsStored.claim book bookedAfter)) (h_storeWhenFree : (Rooms.storeWhenFree.claim book)), False

end Obl

namespace Obl

/-- No world meets bookWhenFree. -/
@[frflow_defs] def unsat : Prop :=
  ∀ (bookedAfter : Booking → World → (List Booking)) (booked : World → (List Booking)), ¬ (Rooms.bookWhenFree.claim bookedAfter booked)

end Obl

namespace Obl

/-- bookWhenFree is met by doing nothing (booked, bookedAfter: returning nothing). -/
@[frflow_defs] def idle : Prop :=
  (Rooms.bookWhenFree.claim (fun (x0 : Booking) (x1 : World) => []) (fun (x0 : World) => []))

end Obl

frflow_match_eqns

end Rooms.bookWhenFree

namespace Rooms.acceptedIsAnswered

@[frflow_defs] def claim (book : Booking → (World → (Prop × World))) (accepted : Booking → World → Prop) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (now : World), ((Rooms.neverOverlap now.bookingTable) → ((∀ b ∈ now.bookingTable, (Rooms.bookingsEndAfterStart b)) → (match (book request now) with | (answer, after) => ((accepted request now) = answer)))))))

namespace Obl

/-- No world meets acceptedIsAnswered. -/
@[frflow_defs] def unsat : Prop :=
  ∀ (book : Booking → (World → (Prop × World))) (accepted : Booking → World → Prop), ¬ (Rooms.acceptedIsAnswered.claim book accepted)

end Obl

frflow_match_eqns

end Rooms.acceptedIsAnswered

namespace Rooms.answerWhenFree

@[frflow_defs] def claim (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.bookingTable) → ((∀ b ∈ before.bookingTable, (Rooms.bookingsEndAfterStart b)) → (match (book request before) with | (answer, after) => (answer = (Rooms.free before.bookingTable request))))))))

namespace Obl

/-- Every result of bookIfGranted_run meets answerWhenFree, given what grantWhenFree promise. -/
@[frflow_defs] def impl : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)), (Rooms.answerWhenFree.claim (Rooms.bookIfGranted_run granted))

end Obl

namespace Obl

/-- answerWhenFree holds whatever grantWhenFree says. -/
@[frflow_defs] def vacuous : Prop :=
  ∀ (book : Booking → (World → (Prop × World))) (granted : RoomBookings → Booking → Prop), (Rooms.answerWhenFree.claim book)

end Obl

namespace Obl

/-- grantWhenFree follows from answerWhenFree. -/
@[frflow_defs] def restates : Prop :=
  ∀ (book : Booking → (World → (Prop × World))) (granted : RoomBookings → Booking → Prop), ∀ (h_answerWhenFree : (Rooms.answerWhenFree.claim book)), (Rooms.grantWhenFree.claim granted)

end Obl

namespace Obl

/-- The parts of answerWhenFree contradict each other. -/
@[frflow_defs] def clash : Prop :=
  ∀ (book : Booking → (World → (Prop × World))) (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)), False

end Obl

namespace Obl

/-- No world meets answerWhenFree. -/
@[frflow_defs] def unsat : Prop :=
  ∀ (book : Booking → (World → (Prop × World))), ¬ (Rooms.answerWhenFree.claim book)

end Obl

frflow_match_eqns

end Rooms.answerWhenFree

namespace Rooms.acceptWhenFree

@[frflow_defs] def claim (accepted : Booking → World → Prop) (booked : World → (List Booking)) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (now : World), ((Rooms.neverOverlap now.bookingTable) → ((∀ b ∈ now.bookingTable, (Rooms.bookingsEndAfterStart b)) → ((accepted request now) = (Rooms.free (booked now) request)))))))

namespace Obl

/-- The parts of acceptWhenFree (bookedIsStored, acceptedIsAnswered, answerWhenFree) together make it. -/
@[frflow_defs] def complete : Prop :=
  ∀ (accepted : Booking → World → Prop) (booked : World → (List Booking)) (book : Booking → (World → (Prop × World))), ∀ (h_bookedIsStored : (Rooms.bookedIsStored.claim booked)) (h_acceptedIsAnswered : (Rooms.acceptedIsAnswered.claim book accepted)) (h_answerWhenFree : (Rooms.answerWhenFree.claim book)), (Rooms.acceptWhenFree.claim accepted booked)

end Obl

namespace Obl

/-- acceptWhenFree holds without bookedIsStored. -/
@[frflow_defs] def needed_bookedIsStored : Prop :=
  ∀ (accepted : Booking → World → Prop) (booked : World → (List Booking)) (book : Booking → (World → (Prop × World))), ∀ (h_acceptedIsAnswered : (Rooms.acceptedIsAnswered.claim book accepted)) (h_answerWhenFree : (Rooms.answerWhenFree.claim book)), (Rooms.acceptWhenFree.claim accepted booked)

end Obl

namespace Obl

/-- acceptWhenFree holds without acceptedIsAnswered. -/
@[frflow_defs] def needed_acceptedIsAnswered : Prop :=
  ∀ (accepted : Booking → World → Prop) (booked : World → (List Booking)) (book : Booking → (World → (Prop × World))), ∀ (h_bookedIsStored : (Rooms.bookedIsStored.claim booked)) (h_answerWhenFree : (Rooms.answerWhenFree.claim book)), (Rooms.acceptWhenFree.claim accepted booked)

end Obl

namespace Obl

/-- acceptWhenFree holds without answerWhenFree. -/
@[frflow_defs] def needed_answerWhenFree : Prop :=
  ∀ (accepted : Booking → World → Prop) (booked : World → (List Booking)) (book : Booking → (World → (Prop × World))), ∀ (h_bookedIsStored : (Rooms.bookedIsStored.claim booked)) (h_acceptedIsAnswered : (Rooms.acceptedIsAnswered.claim book accepted)), (Rooms.acceptWhenFree.claim accepted booked)

end Obl

namespace Obl

/-- The parts of acceptWhenFree contradict each other. -/
@[frflow_defs] def clash : Prop :=
  ∀ (accepted : Booking → World → Prop) (booked : World → (List Booking)) (book : Booking → (World → (Prop × World))), ∀ (h_bookedIsStored : (Rooms.bookedIsStored.claim booked)) (h_acceptedIsAnswered : (Rooms.acceptedIsAnswered.claim book accepted)) (h_answerWhenFree : (Rooms.answerWhenFree.claim book)), False

end Obl

namespace Obl

/-- No world meets acceptWhenFree. -/
@[frflow_defs] def unsat : Prop :=
  ∀ (accepted : Booking → World → Prop) (booked : World → (List Booking)), ¬ (Rooms.acceptWhenFree.claim accepted booked)

end Obl

namespace Obl

/-- acceptWhenFree is met by doing nothing (accepted, booked: returning nothing). -/
@[frflow_defs] def idle : Prop :=
  (Rooms.acceptWhenFree.claim (fun (x0 : Booking) (x1 : World) => False) (fun (x0 : World) => []))

end Obl

frflow_match_eqns

end Rooms.acceptWhenFree

namespace Rooms.neverOverlap

@[frflow_defs] def claim : Prop :=
  True

@[frflow_defs] def keeps_book (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.bookingTable) → ((∀ b ∈ before.bookingTable, (Rooms.bookingsEndAfterStart b)) → (match (book request before) with | (result, after) => (Rooms.neverOverlap after.bookingTable)))))))

namespace Obl

/-- Every run of bookIfGranted_run keeps neverOverlap, given what grantWhenFree, grantWhenNoOverlap promise. -/
@[frflow_defs] def cover_book : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)) (h_grantWhenNoOverlap : (Rooms.grantWhenNoOverlap.claim granted)), (Rooms.neverOverlap.keeps_book (Rooms.bookIfGranted_run granted))

end Obl

frflow_match_eqns

end Rooms.neverOverlap

namespace Rooms.bookingsOfTheRoom

@[frflow_defs] def claim : Prop :=
  True

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.bookingTable) → ((∀ b ∈ w.bookingTable, (Rooms.bookingsEndAfterStart b)) → (Rooms.bookingsOfTheRoom (inRoom room w.bookingTable))))))

namespace Obl

/-- Every result of storedBookings's inRoom meets bookingsOfTheRoom, on a world meeting what always holds. -/
@[frflow_defs] def made_inRoom : Prop :=
  (Rooms.bookingsOfTheRoom.makes_inRoom Rooms.StoredBookings.inRoom_of)

end Obl

frflow_match_eqns

end Rooms.bookingsOfTheRoom

namespace Rooms.roomBookingsApart

@[frflow_defs] def claim : Prop :=
  True

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.bookingTable) → ((∀ b ∈ w.bookingTable, (Rooms.bookingsEndAfterStart b)) → (Rooms.roomBookingsApart (inRoom room w.bookingTable))))))

namespace Obl

/-- Every result of storedBookings's inRoom meets roomBookingsApart, on a world meeting what always holds. -/
@[frflow_defs] def made_inRoom : Prop :=
  (Rooms.roomBookingsApart.makes_inRoom Rooms.StoredBookings.inRoom_of)

end Obl

frflow_match_eqns

end Rooms.roomBookingsApart

namespace Rooms.bookingsEndAfterStart

@[frflow_defs] def claim : Prop :=
  True

@[frflow_defs] def keeps_book (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.bookingTable) → ((∀ b ∈ before.bookingTable, (Rooms.bookingsEndAfterStart b)) → (match (book request before) with | (result, after) => (∀ b ∈ after.bookingTable, (Rooms.bookingsEndAfterStart b))))))))

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.bookingTable) → ((∀ b ∈ w.bookingTable, (Rooms.bookingsEndAfterStart b)) → (∀ b ∈ (inRoom room w.bookingTable).bookings, (Rooms.bookingsEndAfterStart b))))))

namespace Obl

/-- Every run of bookIfGranted_run keeps bookingsEndAfterStart, given what grantWhenFree, grantWhenNoOverlap promise. -/
@[frflow_defs] def cover_book : Prop :=
  ∀ (granted : RoomBookings → Booking → Prop), ∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)) (h_grantWhenNoOverlap : (Rooms.grantWhenNoOverlap.claim granted)), (Rooms.bookingsEndAfterStart.keeps_book (Rooms.bookIfGranted_run granted))

end Obl

namespace Obl

/-- Every result of storedBookings's inRoom meets bookingsEndAfterStart, on a world meeting what always holds. -/
@[frflow_defs] def made_inRoom : Prop :=
  (Rooms.bookingsEndAfterStart.makes_inRoom Rooms.StoredBookings.inRoom_of)

end Obl

frflow_match_eqns

end Rooms.bookingsEndAfterStart

namespace Rooms.Whole

namespace Obl

/-- bookedIsStored hold together: some meaning of booked makes each true. -/
@[frflow_defs] def consistent_0 : Prop :=
  ∃ (booked : World → (List Booking)), (Rooms.bookedIsStored.claim booked)

end Obl

namespace Obl

/-- bookedAfterIsStored, acceptedIsAnswered, grantWhenNoOverlap hold together: some meaning of bookedAfter, granted, accepted makes each true. -/
@[frflow_defs] def consistent_1 : Prop :=
  ∃ (bookedAfter : Booking → World → (List Booking)) (granted : RoomBookings → Booking → Prop) (accepted : Booking → World → Prop), (Rooms.bookedAfterIsStored.claim (Rooms.bookIfGranted_run granted) bookedAfter) ∧ (Rooms.acceptedIsAnswered.claim (Rooms.bookIfGranted_run granted) accepted) ∧ (Rooms.grantWhenNoOverlap.claim granted)

end Obl

namespace Obl

/-- Every state storedBookings may start in meets neverOverlap. -/
@[frflow_defs] def start_neverOverlap : Prop :=
  ∀ (s : (List Booking)), (Rooms.startsEmpty s) → (Rooms.neverOverlap s)

end Obl

namespace Obl

/-- Every state storedBookings may start in meets bookingsEndAfterStart. -/
@[frflow_defs] def start_bookingsEndAfterStart : Prop :=
  ∀ (s : (List Booking)), (Rooms.startsEmpty s) → ∀ x ∈ s, (Rooms.bookingsEndAfterStart x)

end Obl

namespace Obl

/-- Some value meets bookingsOfTheRoom. -/
@[frflow_defs] def inhabited_bookingsOfTheRoom : Prop :=
  ∃ (x : RoomBookings), (Rooms.bookingsOfTheRoom x)

end Obl

namespace Obl

/-- Some value meets roomBookingsApart. -/
@[frflow_defs] def inhabited_roomBookingsApart : Prop :=
  ∃ (x : RoomBookings), (Rooms.roomBookingsApart x)

end Obl

namespace Obl

/-- Some value meets bookingsEndAfterStart. -/
@[frflow_defs] def inhabited_bookingsEndAfterStart : Prop :=
  ∃ (x : Booking), (Rooms.bookingsEndAfterStart x)

end Obl

theorem consistent_0 : Obl.consistent_0 :=
  ⟨(fun (now : World) => now.bookingTable), by frflow_witness⟩

#print axioms Rooms.Whole.consistent_0

theorem consistent_1 : Obl.consistent_1 :=
  ⟨(fun (request : Booking) => (fun (now : World) => (Rooms.bookIfGranted_run (fun (held : RoomBookings) => (fun (request : Booking) => (∀ b ∈ held.bookings, (Rooms.noOverlap b request)))) request now).2.bookingTable)), (fun (held : RoomBookings) => (fun (request : Booking) => (∀ b ∈ held.bookings, (Rooms.noOverlap b request)))), (fun (request : Booking) => (fun (now : World) => (Rooms.bookIfGranted_run (fun (held : RoomBookings) => (fun (request : Booking) => (∀ b ∈ held.bookings, (Rooms.noOverlap b request)))) request now).1)), by frflow_witness⟩

#print axioms Rooms.Whole.consistent_1

theorem start_neverOverlap : Obl.start_neverOverlap := by
  frflow_auto

#print axioms Rooms.Whole.start_neverOverlap

theorem start_bookingsEndAfterStart : Obl.start_bookingsEndAfterStart := by
  frflow_auto

#print axioms Rooms.Whole.start_bookingsEndAfterStart

end Rooms.Whole
