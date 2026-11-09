import FrFlowGen.Sharing.viewFollowsShares.Spec
import Proofs.Sharing.Lemmas

/-! Access, as accessContract works it out, is what the purpose's words say: the shares it keeps are those in force
that reach the person (reach) and cover the document (cover), which is what may be viewed (permission); and a
document in the trash (whatIsTrashed, inTrash) gives no access. Viewing is having some access (canViewContract). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.viewFollowsShares.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro access inTheTrash mayView reaches covers inForce inTrash hReach hCover hPerm hTrash hWhat hAccess _ lib t
    p d world
  unfold Sharing.permission.claim at hPerm
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
  simp only [canViewCode, hA, hPerm, hWhat, hTrash]
  by_cases ht : ∃ doc ∈ lib.documents, doc.id_ = d ∧ doc.trashed ≠ none
  · simp [ht]
  · simp only [ht, ite_false, not_false_eq_true, true_and]
    apply propext
    simp only [strongest]
    split
    · next h => obtain ⟨s, hs, _⟩ := h; exact ⟨fun _ => ⟨s, (hf s).1 hs⟩, fun _ => nofun⟩
    · split
      · next _ he =>
        simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
        intro s hs hw hc
        exact List.eq_nil_iff_forall_not_mem.mp he s ((hf s).2 ⟨hs, hw, hc⟩)
      · next _ he =>
        obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ he
        exact ⟨fun _ => ⟨s, (hf s).1 hs⟩, fun _ => nofun⟩

end Sharing.viewFollowsShares.Proofs
