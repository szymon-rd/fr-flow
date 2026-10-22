import FrFlowGen.Crm.WriteContract.Spec

/-! Authored proof that `applyWrite` meets WriteContract: case by case on the change, and on
whether its author's company may make it. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.WriteContract.Proofs
open Crm.WriteContract

/-- The post, for every call, is CrmWrites' statement for one write; the start is consistent. -/
theorem link : Obl.link := by
  unfold Obl.link
  intro m h
  unfold spec at h
  unfold Crm.CrmWrites.spec Crm.StepByStep.spec
  refine ⟨?_, fun s w => ?_⟩
  · simp [Crm.CrmWrites.s_consistent, Crm.CrmWrites.s_initial, Crm.consistentStore]
  · have hp := h s w
    unfold post at hp
    exact ⟨⟨hp.1.1.1, hp.1.1.2⟩, hp.1.2⟩

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro s w
  rcases w with ⟨a, ch⟩
  cases ch with
  | ShareWith id to u => cases u <;> simp only [frflow_defs] <;> split <;> simp_all <;> grind
  | _ => simp only [frflow_defs] <;> split <;> simp_all <;> grind

/-- The root says something here: code that always leaves a share of no stored record fails it. -/
theorem nontrivial : Obl.nontrivial := by
  unfold Obl.nontrivial
  refine ⟨fun _ _ => ⟨[], [⟨1, ⟨"globex"⟩⟩], []⟩, fun h => ?_⟩
  have := (h.1) [⟨⟨"ann@acme", ⟨"acme"⟩⟩, Change.Unshare 1 ⟨"globex"⟩⟩]
  simp [frflow_defs] at this

end Crm.WriteContract.Proofs
