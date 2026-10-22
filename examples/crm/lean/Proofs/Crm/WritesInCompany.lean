import FrFlowGen.Crm.WritesInCompany.Spec
import Proofs.Crm.Lemmas

/-! WritesInCompany from its parts: in a store the CRM reaches, ids are unique (StoreConsistent); on
such a store a write leaves other companies' records, shares and expiries as they were
(WriteContract); and the write side stores the rows about the written record only (SaveWrite), so
what the database then holds of another company is what it held. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.WritesInCompany.Proofs
open Crm.WritesInCompany

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro expire save write h_StoreConsistent h_WriteContract h_SaveWrite
  unfold Crm.WritesInCompany.claim
  intro es w c hc
  have hu := h_StoreConsistent es
  generalize Crm.runOf expire save es = s at hu ⊢
  have hsv := h_SaveWrite s w
  have hw := h_WriteContract s w
  simp only [Crm.SaveWrite.post] at hsv
  simp only [Crm.WriteContract.post] at hw
  simp only [Crm.afterSave]
  rw [hsv]
  exact Crm.Lemmas.holdsAlike_replace s (write s w) (Crm.about w) w.«by».tenant c hc hw.1.1.2 (hw.2 hu).2

end Crm.WritesInCompany.Proofs
