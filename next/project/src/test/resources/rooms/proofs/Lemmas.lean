import FrFlowGen.Rooms.Domain
import FrFlowGen.Rooms.grantWhenFree.Spec

/-! What the proofs of rooms share: the run of `bookIfGranted` on the models, and what a room's bookings of a store
whose bookings never overlap and end after they start meet. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Rooms.Lemmas

/-- The run of `bookIfGranted` on the models: the room's bookings read, the answer granted's, the request added
exactly when granted. -/
theorem run_eq (granted : RoomBookings → Booking → Prop) (request : Booking) (w : World) :
    bookIfGranted_run granted request w =
      (granted ⟨request.room, w.bookingTable.filter (fun b => decide (b.room = request.room))⟩ request,
       if granted ⟨request.room, w.bookingTable.filter (fun b => decide (b.room = request.room))⟩ request
       then { w with bookingTable := w.bookingTable ++ [request] } else w) := by
  by_cases h : granted ⟨request.room, w.bookingTable.filter (fun b => decide (b.room = request.room))⟩ request <;>
    simp [bookIfGranted_run, bookIfGranted, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_within,
      FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_map, FrFlow.runOn_ite, BookingTable.inRoom_onWorld,
      BookingTable.add_onWorld, StoredBookings.inRoom, StoredBookings.add, h]

/-- Bookings that end after they start and share no moment do not overlap, in start and end times. -/
theorem apart_noOverlap (a b : Booking) (ha : bookingsEndAfterStart a) (hb : bookingsEndAfterStart b)
    (h : apart a b) : noOverlap a b := by
  unfold bookingsEndAfterStart at ha hb
  unfold apart covers at h
  unfold noOverlap
  rcases h with h | h
  · exact Or.inl (Or.inl h)
  · by_cases h1 : a.«end» ≤ b.start
    · exact Or.inl (Or.inr h1)
    · by_cases h2 : b.«end» ≤ a.start
      · exact Or.inr h2
      · exfalso
        by_cases hs : a.start ≤ b.start
        · exact h b.start ⟨⟨hs, by omega⟩, ⟨Int.le_refl _, hb⟩⟩
        · exact h a.start ⟨⟨Int.le_refl _, ha⟩, ⟨by omega, by omega⟩⟩

/-- Bookings that end after they start do not overlap exactly when they share no moment. -/
theorem apart_iff_noOverlap {a b : Booking} (ha : bookingsEndAfterStart a) (hb : bookingsEndAfterStart b) :
    apart a b ↔ noOverlap a b := by
  refine ⟨apart_noOverlap a b ha hb, fun h => ?_⟩
  unfold bookingsEndAfterStart at ha hb
  unfold noOverlap at h
  unfold apart covers
  rcases h with (h | h) | h
  · exact Or.inl h
  all_goals exact Or.inr fun t => by omega

/-- A room's bookings of a store whose bookings never overlap and end after they start never overlap. -/
theorem room_apart (store : List Booking) (room : String) (hno : neverOverlap store)
    (hv : ∀ b ∈ store, bookingsEndAfterStart b) :
    roomBookingsApart ⟨room, store.filter (fun b => decide (b.room = room))⟩ := by
  unfold roomBookingsApart neverOverlap at *
  have hs : (store.filter (fun b => decide (b.room = room))).Pairwise apart :=
    hno.sublist List.filter_sublist
  exact hs.imp_of_mem (fun {a b} ha hb hab =>
    apart_noOverlap a b (hv a (List.mem_filter.mp ha).1) (hv b (List.mem_filter.mp hb).1) hab)

/-- A room's bookings of a store are all of that room. -/
theorem room_of (store : List Booking) (room : String) :
    bookingsOfTheRoom ⟨room, store.filter (fun b => decide (b.room = room))⟩ := by
  unfold bookingsOfTheRoom
  intro b hb
  simpa using (List.mem_filter.mp hb).2

/-- A booking of another room leaves a request free. -/
theorem free_filter (held : List Booking) (request : Booking) :
    free (held.filter (fun b => decide (b.room = request.room))) request ↔ free held request := by
  unfold free
  constructor
  · intro h b hb
    by_cases hr : b.room = request.room
    · exact h b (List.mem_filter.mpr ⟨hb, by simp [hr]⟩)
    · unfold apart; exact Or.inl hr
  · intro h b hb
    exact h b (List.mem_filter.mp hb).1

/-- What the calendar's claim gives booking's code: granted on the room's bookings is the store's being free. -/
theorem granted_free (granted : RoomBookings → Booking → Prop) (h : grantWhenFree.claim granted)
    (request : Booking) (hr : bookingsEndAfterStart request) (store : List Booking) (hno : neverOverlap store)
    (hv : ∀ b ∈ store, bookingsEndAfterStart b) :
    granted ⟨request.room, store.filter (fun b => decide (b.room = request.room))⟩ request = free store request := by
  rw [h _ (room_of store request.room) (room_apart store request.room hno hv)
    (fun b hb => hv b (List.mem_filter.mp hb).1) request hr]
  exact propext (free_filter store request)

end Rooms.Lemmas
