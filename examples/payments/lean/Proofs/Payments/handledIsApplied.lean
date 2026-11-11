import FrFlowGen.Payments.handledIsApplied.Spec
import Proofs.Payments.Lemmas

/-! The limits service decided the payment and answered what it recorded. Approved: the accounts service posted
it. Declined: the record says so. The commit touches neither. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.handledIsApplied.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := by
  intro authorise post commit hrecorded hmarked pipeline p
  have said := hrecorded pipeline.spending p
  unfold handleCode
  by_cases happ : (authorise pipeline.spending p).1
  · simp only [happ, ite_true]
    exact ⟨said.1, Or.inr (hmarked pipeline.books p)⟩
  · simp only [happ, ite_false]
    exact ⟨said.1, Or.inl (fun h => happ (said.2.mpr h))⟩

end Payments.handledIsApplied.Proofs
