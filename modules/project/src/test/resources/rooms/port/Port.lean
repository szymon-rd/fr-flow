import FrFlowGen.Old.BookWhenFree.Spec
import FrFlowGen.Old.AcceptWhenFree.Spec
import FrFlowGen.Old.BookedIsStored.Spec
import FrFlowGen.Old.BookedAfterIsStored.Spec
import FrFlowGen.Old.AcceptedIsAnswered.Spec
import FrFlowGen.Old.StoreWhenFree.Spec
import FrFlowGen.Old.AnswerWhenFree.Spec
import FrFlowGen.Old.GrantWhenFree.Spec
import FrFlowGen.Old.GrantWhenNoOverlap.Spec
import FrFlowGen.Old.Domain.Def_startsEmpty
import FrFlowGen.Old.Domain.Def_bookingsOfTheRoom
import FrFlowGen.Rooms.bookWhenFree.Spec
import FrFlowGen.Rooms.acceptWhenFree.Spec
import FrFlowGen.Rooms.bookedIsStored.Spec
import FrFlowGen.Rooms.bookedAfterIsStored.Spec
import FrFlowGen.Rooms.acceptedIsAnswered.Spec
import FrFlowGen.Rooms.storeWhenFree.Spec
import FrFlowGen.Rooms.answerWhenFree.Spec
import FrFlowGen.Rooms.grantWhenFree.Spec
import FrFlowGen.Rooms.grantWhenNoOverlap.Spec
import FrFlowGen.Rooms.Domain
import FrFlowGen.Rooms.Domain.Def_startsEmpty

/-! No statement of rooms is weakened by the port (ARCHITECTURE section 9, equivalence 4): each node's claim as
today's library stated it (`reference/rooms`, put in namespace `Old` over the port's types) is equivalent to the
port's. The two claims about the calendar take a room's bookings apart in today's words (`apart`, over moments) and
in the port's (`noOverlap`, over start and end times, section 2.3): equivalent for bookings that end after they
start, which both claims take as a hypothesis. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Port
open Rooms

theorem bookWhenFree (booked bookedAfter) :
    Old.BookWhenFree.claim booked bookedAfter ↔ Rooms.bookWhenFree.claim bookedAfter booked := by
  constructor <;> intro h <;> (try simp only [frflow_defs, FrFlow.runOn, StateT.run, Id.run] at *) <;> frflow_auto

theorem acceptWhenFree (booked accepted) :
    Old.AcceptWhenFree.claim booked accepted ↔ Rooms.acceptWhenFree.claim accepted booked := by
  constructor <;> intro h <;> (try simp only [frflow_defs, FrFlow.runOn, StateT.run, Id.run] at *) <;> frflow_auto

theorem bookedIsStored (booked) : Old.BookedIsStored.claim booked ↔ Rooms.bookedIsStored.claim booked := by
  constructor <;> intro h <;> (try simp only [frflow_defs, FrFlow.runOn, StateT.run, Id.run] at *) <;> frflow_auto

theorem bookedAfterIsStored (bookedAfter book) :
    Old.BookedAfterIsStored.claim bookedAfter book ↔ Rooms.bookedAfterIsStored.claim book bookedAfter := by
  constructor <;> intro h <;> (try simp only [frflow_defs, FrFlow.runOn, StateT.run, Id.run] at *) <;> frflow_auto

theorem acceptedIsAnswered (accepted book) :
    Old.AcceptedIsAnswered.claim accepted book ↔ Rooms.acceptedIsAnswered.claim book accepted := by
  constructor <;> intro h <;> (try simp only [frflow_defs, FrFlow.runOn, StateT.run, Id.run] at *) <;> frflow_auto

theorem storeWhenFree (book) : Old.StoreWhenFree.claim book ↔ Rooms.storeWhenFree.claim book := by
  constructor <;> intro h <;> (try simp only [frflow_defs, FrFlow.runOn, StateT.run, Id.run] at *) <;> frflow_auto

theorem answerWhenFree (book) : Old.AnswerWhenFree.claim book ↔ Rooms.answerWhenFree.claim book := by
  constructor <;> intro h <;> (try simp only [frflow_defs, FrFlow.runOn, StateT.run, Id.run] at *) <;> frflow_auto

/-- Today's rule of a room's bookings is over moments (`apart`), the port's over start and end times (`noOverlap`,
section 2.3): for bookings that end after they start, the same. -/
theorem roomBookingsApart (held : RoomBookings) (ends : ∀ b ∈ held.bookings, Rooms.bookingsEndAfterStart b) :
    Old.roomBookingsApart held ↔ Rooms.roomBookingsApart held := by
  have iff : ∀ a b : Booking, Rooms.bookingsEndAfterStart a → Rooms.bookingsEndAfterStart b →
      (Old.apart a b ↔ Rooms.noOverlap a b) := by
    intro a b ha hb
    unfold Rooms.bookingsEndAfterStart at ha hb
    simp only [Old.apart, Old.covers, Rooms.noOverlap]
    constructor
    · rintro (h | h)
      · exact .inl (.inl h)
      · by_cases h1 : a.«end» ≤ b.start
        · exact .inl (.inr h1)
        · by_cases h2 : b.«end» ≤ a.start
          · exact .inr h2
          · exfalso
            by_cases hs : a.start ≤ b.start
            · exact h b.start ⟨⟨hs, by omega⟩, ⟨Int.le_refl _, hb⟩⟩
            · exact h a.start ⟨⟨Int.le_refl _, ha⟩, ⟨by omega, by omega⟩⟩
    · rintro ((h | h) | h)
      · exact .inl h
      all_goals exact .inr fun t => by omega
  unfold Old.roomBookingsApart Rooms.roomBookingsApart
  exact ⟨fun h => h.imp_of_mem fun ha hb hab => (iff _ _ (ends _ ha) (ends _ hb)).mp hab,
    fun h => h.imp_of_mem fun ha hb hab => (iff _ _ (ends _ ha) (ends _ hb)).mpr hab⟩

theorem grantWhenFree (granted) : Old.GrantWhenFree.claim granted ↔ Rooms.grantWhenFree.claim granted := by
  unfold Old.GrantWhenFree.claim Rooms.grantWhenFree.claim
  constructor
  · intro h held hRoom hApart hEnds request hReq
    have := h held request hRoom ((roomBookingsApart held hEnds).mpr hApart) hEnds hReq
    simpa only [frflow_defs] using this
  · intro h held request hRoom hApart hEnds hReq
    have := h held hRoom ((roomBookingsApart held hEnds).mp hApart) hEnds request hReq
    simpa only [frflow_defs] using this

theorem grantWhenNoOverlap (granted) :
    Old.GrantWhenNoOverlap.claim granted ↔ Rooms.grantWhenNoOverlap.claim granted := by
  unfold Old.GrantWhenNoOverlap.claim Rooms.grantWhenNoOverlap.claim
  constructor
  · intro h held hRoom hApart hEnds request hReq
    have := h held request hRoom ((roomBookingsApart held hEnds).mpr hApart) hEnds hReq
    simpa only [frflow_defs] using this
  · intro h held request hRoom hApart hEnds hReq
    have := h held hRoom ((roomBookingsApart held hEnds).mp hApart) hEnds request hReq
    simpa only [frflow_defs] using this

/-! The rules: what always holds of the table, of a booking, of a room's bookings, and the table's start. -/

theorem neverOverlap (s : List Booking) : Old.neverOverlap s ↔ Rooms.neverOverlap s := Iff.rfl
theorem bookingsOfTheRoom (h : RoomBookings) : Old.bookingsOfTheRoom h ↔ Rooms.bookingsOfTheRoom h := Iff.rfl
theorem bookingsEndAfterStart (b : Booking) : Old.bookingsEndAfterStart b ↔ Rooms.bookingsEndAfterStart b := Iff.rfl
theorem startsEmpty (s : List Booking) : Old.startsEmpty s ↔ Rooms.startsEmpty s := by
  simp only [frflow_defs]

end Port

#print axioms Port.bookWhenFree
#print axioms Port.acceptWhenFree
#print axioms Port.bookedIsStored
#print axioms Port.bookedAfterIsStored
#print axioms Port.acceptedIsAnswered
#print axioms Port.storeWhenFree
#print axioms Port.answerWhenFree
#print axioms Port.grantWhenFree
#print axioms Port.grantWhenNoOverlap
#print axioms Port.roomBookingsApart
#print axioms Port.neverOverlap
#print axioms Port.bookingsOfTheRoom
#print axioms Port.bookingsEndAfterStart
#print axioms Port.startsEmpty
