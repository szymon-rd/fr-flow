import FrFlowGen.Sharing.ownersKeepTheirDocuments.Spec
import Proofs.Sharing.Lemmas

/-! A transfer that changes the library was asked by the owner, who may edit, of someone who may edit: the document
is then theirs, with their edit share at the front. Unsharing and sharing leave an owner's share alone. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.ownersKeepTheirDocuments.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intros
  refine ⟨⟨fun lib t by_ d to h => ?_, fun lib t by_ what withWhom ho => ?_⟩, fun lib t by_ s ho => ?_⟩
  · have hc := Lemmas.changed h
    refine ⟨⟨hc, ?_⟩, ?_⟩
    · obtain ⟨⟨⟨doc, hd, hid, _⟩, _⟩, _⟩ := id hc
      simp only [transferCode, hc, and_self, ↓reduceIte]
      exact ⟨{ doc with owner := to }, List.mem_map.mpr ⟨doc, hd, by simp [hid]⟩, hid, rfl⟩
    · simp only [transferCode, hc, and_self, ↓reduceIte]
      exact List.mem_cons_self
  · simp only [unshareCode, ho, not_true_eq_false, and_false, ↓reduceIte]
  · simp only [shareCode, ho, not_true_eq_false, and_false, ↓reduceIte]

end Sharing.ownersKeepTheirDocuments.Proofs
