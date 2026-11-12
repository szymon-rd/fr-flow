import FrFlowGen.Payments.Domain

/-! What the proofs of the payment stream share: what the limits service's code leaves once it has authorised a
payment. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Payments.Lemmas
open Payments

/-- A payment authorised is decided: it was already, or its decision was just added. -/
theorem authorised_decided (limits : CardLimits) (p : Payment) :
    recordedLimits_decided (recordedLimits_authorise limits p).2 p.id_ := by
  unfold recordedLimits_authorise recordedLimits_decided
  by_cases hseen : ∃ d ∈ limits.decisions, d.id_ = p.id_
  · simp only [hseen, not_true_eq_false, ite_false]
  · simp only [hseen, not_false_eq_true, ite_true]
    exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl⟩

/-- Authorising a payment already decided answers what is decided of it and changes nothing. -/
theorem decided_authorise (limits : CardLimits) (p : Payment) (seen : recordedLimits_decided limits p.id_) :
    recordedLimits_authorise limits p = (recordedLimits_approved limits p.id_, limits) := by
  unfold recordedLimits_decided at seen
  unfold recordedLimits_authorise recordedLimits_approved
  simp only [seen, not_true_eq_false, ite_false]

end Payments.Lemmas
