import FrFlowGen.Sharing.accessFollowsShares.Spec
import Proofs.Sharing.Lemmas

/-! The purpose over its Declarations, line by line: what may be viewed and edited is its two parts
(viewFollowsShares, editFollowsShares); who changes what is said in the code's words by the parts below it and by the
branches, and the code lets a person edit exactly when the purpose's words say they may (editPermission,
whoMayEdit). What a branch says of every world and of no part of it holds through a quiet one (`Lemmas.quiet_world`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.accessFollowsShares.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro access inTheTrash mayView allowedToEdit mayEdit ownedBy isPending reaches covers reminderDue handle announce
    record hEdit hWho hView hEditF hShare hUnshare hMove hOffers hTrashGone hAsks hOwners hTidy _ _ _ world
  obtain ⟨w₀, q₀, q₁, q₂, q₃, q₄, q₅, q₆⟩ := Lemmas.quiet_world
  obtain ⟨hOffer, _⟩ := hOffers w₀ q₀ q₁ q₂ q₃ q₄ q₅ q₆
  obtain ⟨hTrashed, _⟩ := hTrashGone w₀ q₀ q₁ q₂ q₃ q₄ q₅ q₆
  obtain ⟨⟨⟨hAsk, hAnswer⟩, _⟩, _⟩ := hAsks w₀ q₀ q₁ q₂ q₃ q₄ q₅ q₆
  obtain ⟨⟨hHand, _⟩, _⟩ := hOwners
  unfold Sharing.editPermission.claim at hEdit
  unfold Sharing.whoMayEdit.claim at hWho
  -- The purpose's "may edit" is the code's: the same shares, in force, reaching and covering.
  have hE : ∀ lib t p x, mayEdit lib t p x → allowedToEdit lib t p x world := fun lib t p x h => by
    rw [hWho]; rw [hEdit] at h; exact h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨fun lib t p d => ⟨hView lib t p d world, hEditF lib t p d world⟩,
    fun lib t by_ s h => hE _ _ _ _ (hShare lib t by_ s h)⟩,
    fun lib t by_ what withWhom h => hE _ _ _ _ (hUnshare lib t by_ what withWhom h)⟩,
    fun lib t by_ d into h => ?_⟩,
    fun lib t by_ to what level h => hE _ _ _ _ ((hOffer lib t by_ to what level).1.1 h)⟩,
    fun lib t p what h => (hOffer lib t p p what Level.View).2 h⟩,
    fun lib t by_ d h => hE _ _ _ _ ((hTrashed lib t by_ d).1 h)⟩, hAsk⟩,
    fun lib t by_ p w h => hE _ _ _ _ ((hAnswer lib t by_ p w).1 h)⟩,
    fun lib t by_ d to h => ?_⟩, hTidy⟩
  · have hm := hMove lib t by_ d into h
    simp only [mayMove] at hm
    exact ⟨hE _ _ _ _ hm.1, fun f hf => hE _ _ _ _ (hm.2 f hf).2⟩
  · have hh := (hHand lib t by_ d to).1 h
    simp only [mayHandOn] at hh
    exact hE _ _ _ _ hh.1.2

end Sharing.accessFollowsShares.Proofs
