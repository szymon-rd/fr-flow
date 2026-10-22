import FrFlowGen.Crm.WriteContract.Spec

/-! Authored proof that `applyWrite` meets WriteContract: case by case on the change, and on
whether its author's company may make it. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.WriteContract.Proofs
open Crm.WriteContract

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro s w
  rcases w with ⟨a, ch⟩
  cases ch <;> simp only [frflow_defs] <;> split <;> grind

end Crm.WriteContract.Proofs
