import Dump
import AuthDump

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Rooms

/-- The room's bookings the store gives: those of the request's room, in the order held. -/
abbrev roomOf (store : List Booking) (room : String) : RoomBookings :=
  RoomBookings.mk (store.filter (fun b => decide (b.room = room)))

/-- The run of `bookIfGranted` on the models: the room's bookings read, the answer granted's, the booking the request
asks for added exactly when granted. -/
theorem run_eq (granted : RoomBookings → Booking → Prop) (request : Request) (w : World) :
    bookIfGranted_run granted request w =
      (granted (roomOf w.store request.room) (asBooking request),
       if granted (roomOf w.store request.room) (asBooking request)
       then { w with store := w.store ++ [asBooking request] } else w) := by
  by_cases h : granted (roomOf w.store request.room) (asBooking request) <;>
    simp [bookIfGranted_run, bookIfGranted, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_within,
      FrFlow.runOn_get, FrFlow.runOn_set, FrFlow.runOn_map, FrFlow.runOn_ite, Bookings.inRoom_onWorld,
      Bookings.add_onWorld, Stored.inRoom, Stored.add, roomOf, h]

/-- The booking a request asks for is in the request's room. -/
theorem asBooking_room (r : Request) : (asBooking r).room = r.room := rfl

/-- What the form sends ends after it starts, so the booking made from it does: `endsAfterStart` from `fromTheForm`. -/
theorem asBooking_ends (r : Request) (h : fromTheForm r) : endsAfterStart (asBooking r) := by
  unfold fromTheForm at h
  unfold endsAfterStart asBooking
  exact h

/-- Bookings that end after they start and share no moment do not overlap, in start and end times. -/
theorem apart_noOverlap (a b : Booking) (ha : endsAfterStart a) (hb : endsAfterStart b) (h : apart a b) :
    noOverlap a b := by
  unfold endsAfterStart at ha hb
  unfold apart at h
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

/-- made_inRoom of roomBookingsApart, as a lemma: a room's bookings of a store that never overlaps never overlap. -/
theorem room_apart (store : List Booking) (room : String) (hno : neverOverlap store)
    (hv : ∀ b ∈ store, endsAfterStart b) : roomBookingsApart (roomOf store room) := by
  unfold roomBookingsApart neverOverlap at *
  have hs : (store.filter (fun b => decide (b.room = room))).Pairwise apart :=
    hno.sublist List.filter_sublist
  exact hs.imp_of_mem (fun {a b} ha hb hab =>
    apart_noOverlap a b (hv a (List.mem_filter.mp ha).1) (hv b (List.mem_filter.mp hb).1) hab)

theorem roomBookingsApart_made_inRoom : roomBookingsApart.Obl.made_inRoom := by
  intro room w hno hv
  have : Stored.inRoom_of room w.store = roomOf w.store room := by
    simp [Stored.inRoom_of, Stored.inRoom, roomOf]
  rw [this]
  exact room_apart w.store room hno hv

theorem endsAfterStart_made_inRoom : endsAfterStart.Obl.made_inRoom := by
  intro room w _ hv b hb
  have : Stored.inRoom_of room w.store = roomOf w.store room := by
    simp [Stored.inRoom_of, Stored.inRoom, roomOf]
  rw [this] at hb
  exact hv b (List.mem_filter.mp hb).1

/-- A booking of another room leaves a request free. -/
theorem isFree_filter (held : List Booking) (request : Booking) :
    isFree (held.filter (fun b => decide (b.room = request.room))) request ↔ isFree held request := by
  unfold isFree
  constructor
  · intro h b hb
    by_cases hr : b.room = request.room
    · exact h b (List.mem_filter.mpr ⟨hb, by simp [hr]⟩)
    · unfold apart; exact Or.inl hr
  · intro h b hb
    exact h b (List.mem_filter.mp hb).1

/-- What the calendar's claim gives the code: granted on the room's bookings is the store's being free; the room's
bookings meet what always holds of them by `room_apart`. -/
theorem granted_free (granted : RoomBookings → Booking → Prop) (h : grantWhenFree.claim granted)
    (request : Booking) (hr : endsAfterStart request) (store : List Booking) (hno : neverOverlap store)
    (hv : ∀ b ∈ store, endsAfterStart b) :
    granted (roomOf store request.room) request = isFree store request := by
  rw [h _ (fun b hb => hv b (List.mem_filter.mp hb).1) (room_apart store request.room hno hv) request hr]
  exact propext (isFree_filter store request)

theorem bookWhenFree_impl : bookWhenFree.Obl.impl := by
  intro granted h request hr before hno hv
  rw [run_eq]
  have hg := granted_free granted h (asBooking request) (asBooking_ends request hr) before.store hno hv
  rw [asBooking_room] at hg
  by_cases hf : isFree before.store (asBooking request)
  · have hy : granted (roomOf before.store request.room) (asBooking request) := hg ▸ hf
    simp [hy, hf]
  · have hn : ¬granted (roomOf before.store request.room) (asBooking request) := hg ▸ hf
    simp [hn, hf]

theorem neverOverlap_cover_book : neverOverlap.Obl.cover_book := by
  intro granted h _ request hr before hno hv
  rw [run_eq]
  have hg := granted_free granted h (asBooking request) (asBooking_ends request hr) before.store hno hv
  rw [asBooking_room] at hg
  by_cases hf : isFree before.store (asBooking request)
  · have hy : granted (roomOf before.store request.room) (asBooking request) := hg ▸ hf
    simp only [hy, ite_true]
    unfold neverOverlap at *
    rw [List.pairwise_append]
    refine ⟨hno, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    simp at hb; subst hb; exact hf a ha
  · have hn : ¬granted (roomOf before.store request.room) (asBooking request) := hg ▸ hf
    simp only [hn, ite_false]; exact hno

theorem endsAfterStart_cover_book : endsAfterStart.Obl.cover_book := by
  intro granted _ _ request hr before _ hv
  rw [run_eq]
  by_cases hy : granted (roomOf before.store request.room) (asBooking request)
  · simp only [hy, ite_true]
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hv b hb
    · simp at hb; subst hb; exact asBooking_ends request hr
  · simp only [hy, ite_false]; exact hv

theorem answersWhetherBooked_impl : answersWhetherBooked.Obl.impl := by
  intro granted _ _ request _ before _ _
  rw [run_eq]
  by_cases hy : granted (roomOf before.store request.room) (asBooking request)
  · have grown : ¬(before.store ++ [asBooking request] = before.store) := fun e => by
      have := congrArg List.length e; simp at this
    simp [hy, grown]
  · simp [hy]

/-! The examples, checked against the claims as FrFlow tries them (`frflow_example`, within its budget): each
hypothesis, last first, as a rewrite of the Definition, its guards and what is left decided. -/
theorem example_0 : Whole.Obl.example_0 := by intro granted h_1 h_2; frflow_example h_2 h_1
theorem example_1 : Whole.Obl.example_1 := by intro granted h_1 h_2; frflow_example h_2 h_1
theorem example_2 : Whole.Obl.example_2 := by intro granted h_1 h_2; frflow_example h_2 h_1

end Rooms

#print axioms Rooms.bookWhenFree_impl
#print axioms Rooms.neverOverlap_cover_book
#print axioms Rooms.endsAfterStart_cover_book
#print axioms Rooms.answersWhetherBooked_impl
#print axioms Rooms.roomBookingsApart_made_inRoom
#print axioms Rooms.endsAfterStart_made_inRoom
#print axioms Rooms.Whole.consistent_0
#print axioms Rooms.Whole.inhabited_endsAfterStart
#print axioms Rooms.Whole.inhabited_roomBookingsApart
#print axioms Rooms.Whole.start_neverOverlap
#print axioms Rooms.Whole.start_endsAfterStart
#print axioms Rooms.example_0
#print axioms Rooms.example_1
#print axioms Rooms.example_2
#print axioms Auth.Whole.consistent_0
#print axioms Auth.Whole.consistent_1
#print axioms Auth.Whole.consistent_2
#print axioms Auth.Bottom.consistent_0
