import FrFlowGen.Payments.assessAnswersWhatIsRecorded.Spec
import Proofs.Payments.Lemmas

/-! The answer is read from the record after the decision, so it is the decision recorded; and the payment is
decided: it was already, or its decision was just added. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.assessAnswersWhatIsRecorded.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := by
  intro spending p
  refine ⟨?_, rfl⟩
  unfold assessCode
  by_cases hseen : decided spending p.id_
  · simp only [hseen, not_true_eq_false, ite_false]
  · simp only [hseen, not_false_eq_true, ite_true]
    exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl⟩

end Payments.assessAnswersWhatIsRecorded.Proofs
