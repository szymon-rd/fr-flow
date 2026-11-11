import FrFlowGen.Payments.blindAppliesThePayment.Spec
import Proofs.Payments.Lemmas

/-! The limits service decided the payment and answered what it recorded. Approved: the blind accounts posted it and
marked it. Declined: the record says so. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Payments.blindAppliesThePayment.Proofs
open Payments Payments.Lemmas

theorem impl : Obl.impl := by
  intro authorise commit hrecorded _ _ _ _ pipeline p
  have said := hrecorded pipeline.spending p
  unfold blindCode
  by_cases happ : (authorise pipeline.spending p).1
  · simp only [happ, ite_true]
    exact ⟨said.1, Or.inr (List.mem_cons_self ..)⟩
  · simp only [happ, ite_false]
    exact ⟨said.1, Or.inl (fun h => happ (said.2.mpr h))⟩

end Payments.blindAppliesThePayment.Proofs
