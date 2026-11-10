import FrFlowGen.Payments.idsStayDistinct.Spec
import Proofs.Payments.Lemmas

/-! Authored proofs of the obligations of idsStayDistinct. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Payments.idsStayDistinct.Proofs
open Payments.idsStayDistinct

theorem cover_pay : Obl.cover_pay := by
  unfold Obl.cover_pay
  intro p before hd
  have hd' := Payments.Lemmas.applied_distinct before.books p hd
  by_cases hp : Payments.payable before.books p
  · simp only [frflow_defs] at hp hd hd' ⊢
    simp only [hp, frflow_defs]
    simpa using hd'
  · simp only [frflow_defs] at hp hd ⊢
    simp only [hp, frflow_defs]
    simpa using hd

end Payments.idsStayDistinct.Proofs
