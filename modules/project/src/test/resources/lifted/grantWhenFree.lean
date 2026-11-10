import FrFlowGen.Calendar.grantWhenFree.Spec

/-! The claim over moments, of the calendar's code, from the claim over start and end times: two bookings that end
after they start are apart exactly when they do not overlap (rooms' own lemma), so the two claims give the code the
same answer. The code is the `def` FrFlow printed from the plain Scala (`Calendar.grantedCode`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Calendar.grantWhenFree.Proofs

theorem apart_iff_noOverlap {a b : Booking} (ha : bookingsEndAfterStart a) (hb : bookingsEndAfterStart b) :
    apart a b ↔ noOverlap a b := by
  simp only [apart, shareNoMoment, noOverlap, covers, bookingsEndAfterStart] at *
  constructor
  · rintro (h | h)
    · exact .inl (.inl h)
    · have := h (max a.start b.start); omega
  · rintro ((h | h) | h)
    · exact .inl h
    all_goals exact .inr fun t => by omega

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro h
  unfold claim
  intro held hEnds request hRequest
  rw [h held hEnds request hRequest]
  simp only [free]
  exact propext (forall₂_congr fun b hb => (apart_iff_noOverlap (hEnds b hb) hRequest).symm)

end Calendar.grantWhenFree.Proofs
