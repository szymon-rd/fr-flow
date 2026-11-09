import FrFlowGen.Sharing.editFollowsShares.Spec
import Proofs.Sharing.Lemmas

/-! Access, as accessContract works it out, is what the purpose's words say: the shares it keeps are those in force
that reach the person (reach) and cover the document (cover); it is edit exactly when one of them is an edit share,
which is what may be edited (whoMayEdit); and a document in the trash (whatIsTrashed, inTrash) gives no access.
Editing is having edit access (canEditContract). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.editFollowsShares.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro access inTheTrash allowedToEdit reaches covers inTrash inForce hReach hCover hTrash hWho hWhat hAccess _ lib t
    p d world
  unfold Sharing.whoMayEdit.claim at hWho
  unfold Sharing.whatIsTrashed.claim at hWhat
  unfold Sharing.inTrash.claim at hTrash
  have hR := hReach
  have hC := hCover
  unfold Sharing.reach.claim at hR
  unfold Sharing.cover.claim at hC
  have hf : ∀ s, s ∈ List.filter (fun s => decide ((inForce s t ∧ s.withWhom ∈ granteesOf lib p) ∧
      s.what ∈ placesOf lib d)) lib.shares ↔ s ∈ lib.shares ∧ ((inForce s t ∧ reaches lib s p) ∧
        covers lib s (Target.Doc d)) := by
    intro s
    rw [List.mem_filter, decide_eq_true_eq, Lemmas.with_iff, Lemmas.of_iff, hR, hC]
    cases s.what <;> rfl
  have hA := hAccess lib t p d
  simp only [canEditCode, hA, hWho, hWhat, hTrash]
  by_cases ht : ∃ doc ∈ lib.documents, doc.id_ = d ∧ doc.trashed ≠ none
  · simp [ht]
  · simp only [ht, ite_false, not_false_eq_true, true_and]
    apply propext
    simp only [strongest]
    split
    · next h =>
      obtain ⟨s, hs, hl⟩ := h
      exact ⟨fun _ => ⟨s, (hf s).1 hs |>.1, (hf s).1 hs |>.2, hl⟩, fun _ => rfl⟩
    · next h =>
      constructor
      · intro he; split at he <;> simp at he
      · rintro ⟨s, hs, hm, hl⟩; exact absurd ⟨s, (hf s).2 ⟨hs, hm⟩, hl⟩ h

end Sharing.editFollowsShares.Proofs
