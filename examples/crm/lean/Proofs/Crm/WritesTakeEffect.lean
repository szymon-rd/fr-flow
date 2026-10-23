import FrFlowGen.Crm.WritesTakeEffect.Spec
import Proofs.Crm.Lemmas

/-! WritesTakeEffect from its parts: the write leads to a store holding what was asked
(WriteContract), and the write side stores that store's rows about the written record (SaveWrite);
what was asked is about those rows only. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.WritesTakeEffect.Proofs
open Crm.WritesTakeEffect

theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  unfold Crm.WritesTakeEffect.claim
  intro s w
  have hSaved := h_SaveWrite s w
  have hWrite := h_WriteContract s w
  simp only [Crm.SaveWrite.post] at hSaved
  simp only [Crm.WriteContract.post] at hWrite
  obtain ⟨⟨_, hTakes⟩, _⟩ := hWrite
  simp only [Crm.afterSave]
  rw [hSaved]
  exact Crm.Lemmas.takesEffect_replace s (write s w) w hTakes

end Crm.WritesTakeEffect.Proofs
