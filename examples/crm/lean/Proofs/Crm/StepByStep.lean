import FrFlowGen.Crm.StepByStep.Spec

/-! Authored proof that StepByStep refines WritesKeepStore: every store reached by writes is
consistent, by induction over the writes (`FrFlow.always`), and each write is permitted and takes
effect, since the
store after `ws ++ [w]` is `w` applied to the store after `ws`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.StepByStep.Proofs
open Crm.StepByStep

theorem link : Obl.link := by
  unfold Obl.link
  intro Store Write consistent initial permitted effect m h
  simp only [frflow_defs] at *
  obtain ⟨h0, hs⟩ := h
  constructor
  · intro ws
    exact FrFlow.always m consistent initial h0 (fun s w hc => (hs s w).1.1 hc) ws
  · intro ws w
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ⟨(hs _ w).1.2, (hs _ w).2⟩

/-- The root says something here: with no store consistent, no model meets it. -/
theorem nontrivial : Obl.nontrivial := by
  unfold Obl.nontrivial
  exact ⟨Unit, Unit, fun _ => False, (), fun _ _ _ => True, fun _ _ _ => True, fun s _ => s, by simp [frflow_defs]⟩

end Crm.StepByStep.Proofs
