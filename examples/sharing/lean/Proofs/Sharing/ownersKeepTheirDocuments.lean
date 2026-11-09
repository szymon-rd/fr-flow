import FrFlowGen.Sharing.ownersKeepTheirDocuments.Spec
import Proofs.Sharing.Lemmas

/-! The branch is its parts, line by line: who hands a document on and to whom (onlyTheOwnerHandsOn), what the new
owner then has (newOwnerOwnsForGood), and that an owner's own share is neither unshared nor replaced
(nobodyUnsharesAnOwner, nobodyReplacesAnOwner). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.ownersKeepTheirDocuments.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro inForce reaches covers mayEdit _ hHand _ _ _
  refine ⟨⟨fun lib t by_ d to => ⟨hHand lib t by_ d to, fun h => ?_⟩, fun lib t by_ what withWhom ho => ?_⟩,
    fun lib t by_ s ho => ?_⟩
  -- An owner's own share left alone, of the code (the parts state it for every word the code calls).
  rotate_left
  · simp only [unshareCode, ho, not_true_eq_false, and_false, ↓reduceIte]
  · simp only [shareCode, ho, not_true_eq_false, and_false, ↓reduceIte]
  -- What the new owner has, of the code (the part states it for every word the code calls).
  have hc := Lemmas.changed h
  obtain ⟨⟨⟨doc, hd, hid, _⟩, _⟩, _⟩ := id hc
  simp only [ownsForGood]
  unfold transferCode
  split
  · exact ⟨⟨{ doc with owner := to }, List.mem_map.mpr ⟨doc, hd, by simp [hid]⟩, hid, rfl⟩, List.mem_cons_self⟩
  · contradiction

end Sharing.ownersKeepTheirDocuments.Proofs
