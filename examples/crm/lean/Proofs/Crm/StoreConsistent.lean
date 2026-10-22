import FrFlowGen.Crm.StoreConsistent.Spec
import Proofs.Crm.Lemmas

/-! StoreConsistent from its parts: every store the CRM reaches has unique ids, by induction over the
events (`FrFlow.always`). The empty store has them; a saved write keeps them (WriteContract keeps them
in the store the write leads to, SaveWrite stores that store's rows about the record); a run of the
expiry job keeps the records (SharesExpire). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.StoreConsistent.Proofs
open Crm.StoreConsistent

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro expire save write h_WriteContract h_SaveWrite h_SharesExpire
  unfold Crm.StoreConsistent.claim
  intro es
  simp only [Crm.runOf]
  apply FrFlow.always (fun s e => Crm.stepOf expire save s e) Crm.idsUnique
  · simp [Crm.idsUnique]
  · intro s e hs
    cases e with
    | Wrote w =>
      have hsv := h_SaveWrite s w
      have hw := h_WriteContract s w
      simp only [Crm.SaveWrite.post] at hsv
      simp only [Crm.WriteContract.post] at hw
      simp only [Crm.stepOf, Crm.afterSave]
      rw [hsv]
      exact Crm.Lemmas.idsUnique_replace s (write s w) (Crm.about w) hs (hw.2 hs).1
    | Expired now =>
      have he := h_SharesExpire s now
      simp only [Crm.SharesExpire.post, Crm.endsDueAt] at he
      simp only [Crm.stepOf, Crm.idsUnique] at hs ⊢
      rw [he.1]
      exact hs

end Crm.StoreConsistent.Proofs
