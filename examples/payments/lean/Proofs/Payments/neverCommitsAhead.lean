import FrFlowGen.Payments.neverCommitsAhead.Spec

/-! The first two steps (the limits service's, the accounts service's) leave the checkpoint as it was, so the
position with it. The last is the commit: by then the payment is applied. The limits service recorded its decision
(`authorisedIsRecorded`); the other calls left it decided as it was; if it was approved the accounts service
marked it posted (`postedIsMarked`), and the other calls left it posted. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Payments.neverCommitsAhead.Proofs
open Payments

theorem impl : Obl.impl := by
  intro authorise post commit decided approved posted position recorded marked processor p between others step taken
  obtain ⟨dec1, ans1⟩ := recorded processor.limits p
  by_cases ok : (authorise processor.limits p).1
  · have ap1 : approved (authorise processor.limits p).2 p.id_ := ans1 ▸ ok
    simp [streamProcessor_handle_among, streamProcessor_decided, streamProcessor_approved, streamProcessor_posted,
      streamProcessor_position, streamProcessor_applied, ok, dec1, ap1] at others taken ⊢
    generalize (between 2).getD _ = n2 at others taken
    generalize (between 3).getD _ = n3 at others taken
    obtain ⟨⟨⟨dec2, _⟩, _⟩, kept, keptPosted⟩ := others
    rcases taken with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨(kept dec2).1, Or.inr (keptPosted (marked n2.accounts p))⟩
  · have ap1 : ¬ approved (authorise processor.limits p).2 p.id_ := ans1 ▸ ok
    simp [streamProcessor_handle_among, streamProcessor_decided, streamProcessor_approved, streamProcessor_posted,
      streamProcessor_position, streamProcessor_applied, ok, dec1, ap1] at others taken ⊢
    generalize (between 3).getD _ = n3 at others taken
    obtain ⟨⟨dec3, no3⟩, _⟩ := others
    rcases taken with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨dec3, Or.inl no3⟩

end Payments.neverCommitsAhead.Proofs
