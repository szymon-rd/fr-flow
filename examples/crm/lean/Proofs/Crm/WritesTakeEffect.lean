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
  intro save write h_WriteContract h_SaveWrite
  unfold Crm.WritesTakeEffect.claim
  intro s w
  have hsv := h_SaveWrite s w
  have hw := h_WriteContract s w
  simp only [Crm.SaveWrite.post] at hsv
  simp only [Crm.WriteContract.post] at hw
  simp only [Crm.afterSave]
  rw [hsv]
  exact Crm.Lemmas.takesEffect_replace s (write s w) w hw.1.2

end Crm.WritesTakeEffect.Proofs
