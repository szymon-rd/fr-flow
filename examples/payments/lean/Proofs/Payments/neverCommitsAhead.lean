import FrFlowGen.Payments.neverCommitsAhead.Spec

/-! The first two steps (the card limits', the ledger's) leave the consumer's offsets as they were, so the
committed offset with them. The last is the commit: by then the payment is applied. The card limits recorded their
decision (`authorisedIsRecorded`); the other calls left it decided as it was; if it was approved the ledger marked
it posted (`postedIsMarked`), and the other calls left it posted. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Payments.neverCommitsAhead.Proofs
open Payments

theorem impl : Obl.impl := by
  intro authorise post commit decided approved posted committed recorded marked handler p between others step taken
  obtain ⟨dec1, ans1⟩ := recorded handler.limits p
  by_cases ok : (authorise handler.limits p).1
  · have ap1 : approved (authorise handler.limits p).2 p.id_ := ans1 ▸ ok
    simp [streamPaymentHandler_handle_among, streamPaymentHandler_limits_held, streamPaymentHandler_ledger_held,
      streamPaymentHandler_offsets_held, ok, dec1, ap1] at others taken ⊢
    generalize (between 2).getD _ = n2 at others taken
    generalize (between 3).getD _ = n3 at others taken
    obtain ⟨⟨⟨dec2, _⟩, _⟩, kept, keptPosted⟩ := others
    rcases taken with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨(kept dec2).1, Or.inr (keptPosted (marked n2.ledger p))⟩
  · have ap1 : ¬ approved (authorise handler.limits p).2 p.id_ := ans1 ▸ ok
    simp [streamPaymentHandler_handle_among, streamPaymentHandler_limits_held, streamPaymentHandler_ledger_held,
      streamPaymentHandler_offsets_held, ok, dec1, ap1] at others taken ⊢
    generalize (between 3).getD _ = n3 at others taken
    obtain ⟨⟨dec3, no3⟩, _⟩ := others
    rcases taken with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨dec3, Or.inl no3⟩

end Payments.neverCommitsAhead.Proofs
