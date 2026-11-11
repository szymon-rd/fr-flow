import FrFlowGen.Payments.Whole.Spec
import Proofs.Payments.Lemmas

/-! The conditions of the stream's claims FrFlow's search found no values for, each shown to hold of an empty
pipeline, or of books in which one payment is marked as posted. And the stream's examples FrFlow's automation
does not decide within an example's budget, each its code's run on the pipeline and the schedule given: the
payment declined for the limit, the payment delivered again, the payment another instance handles between two
steps, the eager processor stopped after its commit, and the blind processor charging a card twice. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Payments.Whole.Proofs
open Payments

theorem satisfiable_1_postedOnce : Obl.satisfiable_1_postedOnce :=
  ⟨Pipeline.mk (Spending.mk 100 []) (Books.mk [] []) 0, fun _ => none, "p1", Payment.mk 0 "p1" "card" "cafe" 80 1,
    by simp [orderly]⟩

theorem satisfiable_1_leavesOthersUndisturbed : Obl.satisfiable_1_leavesOthersUndisturbed :=
  ⟨Pipeline.mk (Spending.mk 100 []) (Books.mk [] []) 0, fun _ => none, "p1", Payment.mk 0 "p1" "card" "cafe" 80 1,
    by simp [orderly, withinLimits]⟩

theorem satisfiable_1_postKeepsPosted : Obl.satisfiable_1_postKeepsPosted :=
  ⟨Books.mk [] ["p1"], "p1", Payment.mk 0 "p1" "card" "cafe" 80 1, by simp⟩

theorem example_PaymentsExamples_1 : Obl.example_PaymentsExamples_1 := by
  intro _ _ _ _ _ _ _
  simp [handleCode, authoriseCode, assessCode, postCode, postOnceCode, commitCode, advanceCode, decided, approved,
    spent, made]

theorem example_PaymentsExamples_2 : Obl.example_PaymentsExamples_2 := by
  intro _ _ _ _ _ _ _
  simp [handleCode, authoriseCode, assessCode, postCode, postOnceCode, commitCode, advanceCode, decided, approved,
    spent, made]

theorem example_PaymentsExamples_4 : Obl.example_PaymentsExamples_4 := by
  intro _ _ _ _ _ _
  simp [handleAmongOthersCode, assessCode, postOnceCode, advanceCode, others, undisturbed, withinLimits, orderly,
    decided, approved, spent, made]

theorem example_PaymentsExamples_5 : Obl.example_PaymentsExamples_5 := by
  intro _ _
  simp [eagerAmongOthersCode, assessCode, postOnceCode, advanceCode, others, undisturbed, withinLimits, orderly,
    applied, decided, approved, spent, made]

theorem example_PaymentsExamples_6 : Obl.example_PaymentsExamples_6 := by
  intro _ _
  simp [blindCode, authoriseCode, assessCode, commitCode, advanceCode, decided, approved, spent, made]

end Payments.Whole.Proofs
