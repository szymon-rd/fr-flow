import FrFlowGen.Crm.WritesOnlyAsAsked.Spec
import Proofs.Crm.Lemmas

/-! WritesOnlyAsAsked from its parts: the write leads to a store that changes nothing it did not ask
(WriteContract), and the write side stores only that store's rows about the written record
(SaveWrite): every other row is the one the database held. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.WritesOnlyAsAsked.Proofs
open Crm.WritesOnlyAsAsked

theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  unfold Crm.WritesOnlyAsAsked.claim
  intro s w
  have hSaved := h_SaveWrite s w
  have hWrite := h_WriteContract s w
  simp only [Crm.SaveWrite.post] at hSaved
  simp only [Crm.WriteContract.post] at hWrite
  obtain ⟨_, hOnly⟩ := hWrite
  simp only [Crm.afterSave]
  rw [hSaved]
  exact Crm.Lemmas.onlyAsked_replace s (write s w) w hOnly

end Crm.WritesOnlyAsAsked.Proofs
