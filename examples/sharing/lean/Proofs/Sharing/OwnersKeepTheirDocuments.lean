import FrFlowGen.Sharing.OwnersKeepTheirDocuments.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of OwnersKeepTheirDocuments. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.OwnersKeepTheirDocuments.Proofs
open Sharing.OwnersKeepTheirDocuments

/-- A transfer that changes the library was made by the owner, who may edit, to someone who may edit (TransferContract):
the document it names is then theirs, with their edit share at the front; and unsharing and sharing leave an owner's share alone
(UnshareContract, ShareContract). -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro transfer inForce unshare share hS hU hT
  unfold Sharing.OwnersKeepTheirDocuments.claim
  refine ⟨⟨fun lib t by_ d to h => ?_, fun lib t by_ what withWhom ho => ?_⟩, fun lib t by_ s ho => ?_⟩
  · have hc := Sharing.Lemmas.changed (by rw [hT lib t by_ d to] at h; exact h)
    refine ⟨⟨hc, ?_⟩, ?_⟩
    · obtain ⟨⟨⟨doc, hd, hid, _⟩, _⟩, _⟩ := id hc
      rw [hT lib t by_ d to]; simp only [hc, and_self, ↓reduceIte]
      exact ⟨{ doc with owner := to }, List.mem_map.mpr ⟨doc, hd, by simp [hid]⟩, hid, rfl⟩
    · rw [hT lib t by_ d to]; simp only [hc, and_self, ↓reduceIte]
      exact List.mem_cons_self
  · rw [hU lib t by_ what withWhom]
    simp only [ho, not_true_eq_false, and_false, ↓reduceIte]
  · rw [hS lib t by_ s]
    simp only [ho, not_true_eq_false, and_false, ↓reduceIte]

end Sharing.OwnersKeepTheirDocuments.Proofs
