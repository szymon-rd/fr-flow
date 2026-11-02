import FrFlowGen.Sharing.accessFollowsShares.Spec
import Proofs.Sharing.Lemmas

/-! The purpose over its Declarations: what may be viewed (permission), what may be edited (whoMayEdit) and what is
in the trash (whatIsTrashed), each said in terms of the code's words. Access, as accessContract works it out, is what
they say: the shares it keeps are those in force that reach the person (reach) and cover the document (cover), and a
document in the trash gives no access (inTrash). The code lets a person edit exactly when the purpose's words say
they may (editPermission, whoMayEdit). The branches give the second half: invitations, the trash, housekeeping,
access requests and ownership each say who may change them; sharing, unsharing and moving say so of themselves
(their contracts' code). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.accessFollowsShares.Proofs
open Sharing

/-- Who a share must be with, as accessContract lists them, is whom it reaches. -/
theorem with_iff (lib : Library) (p : PersonId) (g : Grantee) :
    g ∈ granteesOf lib p ↔ (match g with
      | Grantee.Person q => q = p
      | Grantee.Team t => ∃ team ∈ lib.teams, team.id_ = t ∧ p ∈ team.members) := by
  cases g with
  | Person q => simp [granteesOf]
  | Team t =>
    simp only [granteesOf, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq, reduceCtorEq, false_or,
      Grantee.Team.injEq]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, h3⟩; exact ⟨a, h1, h3, h2⟩
    · rintro ⟨a, h1, h3, h2⟩; exact ⟨a, ⟨h1, h2⟩, h3⟩

/-- What a share must be of, as accessContract lists it, is what covers the document. -/
theorem of_iff (lib : Library) (d : DocumentId) (t : Target) :
    t ∈ placesOf lib d ↔ (match t with
      | Target.Doc e => Target.Doc d = Target.Doc e
      | Target.InFolder f => ∃ doc ∈ lib.documents, doc.id_ = d ∧ f ∈ doc.folders) := by
  cases t with
  | Doc e => simp [placesOf, eq_comm]
  | InFolder f =>
    simp only [placesOf, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
      reduceCtorEq, false_or, Target.InFolder.injEq]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, b, h3, rfl⟩; exact ⟨a, h1, h2, h3⟩
    · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, ⟨h1, h2⟩, f, h3, rfl⟩

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro access inTheTrash mayView allowedToEdit mayEdit ownedBy isPending reaches covers inTrash events startedAt
    reminderDue handle announce record hReach hCover hPerm hEdit hTrash _ hWho hWhat hOffers hTrashGone hTidy hAsks _ _
    _ hAccess _ _ _ _ _ _
  obtain ⟨⟨hOffers, hAccept⟩, _⟩ := hOffers
  obtain ⟨hTrashed, _⟩ := hTrashGone
  obtain ⟨hTidy, _⟩ := hTidy
  obtain ⟨⟨hAsk, hAnswer⟩, _⟩ := hAsks
  unfold Sharing.permission.claim at hPerm
  unfold Sharing.editPermission.claim at hEdit
  unfold Sharing.whoMayEdit.claim at hWho
  unfold Sharing.whatIsTrashed.claim at hWhat
  unfold Sharing.inTrash.claim at hTrash
  -- The purpose's "may edit" is the code's: the same shares, in force, reaching and covering.
  have hE : ∀ lib t p x, mayEdit lib t p x → allowedToEdit lib t p x := fun lib t p x h => by
    rw [hWho]; rw [hEdit] at h; exact h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨fun lib t p d => ?_, fun lib t by_ s h => hE _ _ _ _ ?_⟩,
    fun lib t by_ what withWhom h => hE _ _ _ _ ?_⟩,
    fun lib t by_ d into h => ?_⟩,
    fun lib t by_ to what => ⟨fun h => hE _ _ _ _ ((hOffers lib t by_ to what).1 h),
      fun level h => hE _ _ _ _ (((hOffers lib t by_ to what).2 level).1 h)⟩⟩,
    hAccept⟩, fun lib t by_ d => ⟨fun h => hE _ _ _ _ ((hTrashed lib t by_ d).1 h),
      fun h => hE _ _ _ _ (((hTrashed lib t by_ d).2 h).1)⟩⟩, hAsk⟩,
    fun lib t by_ p d => ⟨fun h => hE _ _ _ _ (((hAnswer lib t by_ p d).1 h).1),
      fun h => hE _ _ _ _ ((hAnswer lib t by_ p d).2 h)⟩⟩,
    fun lib t by_ d to h => hE _ _ _ _ (Lemmas.changed h).1.2⟩, hTidy⟩
  · have hR := hReach
    have hC := hCover
    unfold Sharing.reach.claim at hR
    unfold Sharing.cover.claim at hC
    have hf : ∀ s, s ∈ List.filter (fun s => decide ((inForceCode s t ∧ s.withWhom ∈ granteesOf lib p) ∧
        s.what ∈ placesOf lib d)) lib.shares ↔ s ∈ lib.shares ∧ ((inForceCode s t ∧ reaches lib s p) ∧
          covers lib s (Target.Doc d)) := by
      intro s
      rw [List.mem_filter, decide_eq_true_eq, with_iff, of_iff, hR, hC]
      cases s.what <;> rfl
    have hA := hAccess lib t p d
    simp only [canViewCode, canEditCode, hA, hPerm, hWho, hWhat, hTrash]
    by_cases ht : ∃ doc ∈ lib.documents, doc.id_ = d ∧ doc.trashed ≠ none
    · simp [ht]
    · simp only [ht, ite_false, not_false_eq_true, true_and]
      constructor
      · apply propext
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
      · apply propext
        simp only [strongest]
        split
        · next h =>
          obtain ⟨s, hs, hl⟩ := h
          exact ⟨fun _ => ⟨s, (hf s).1 hs |>.1, (hf s).1 hs |>.2, hl⟩, fun _ => rfl⟩
        · next h =>
          constructor
          · intro he; split at he <;> simp at he
          · rintro ⟨s, hs, hm, hl⟩; exact absurd ⟨s, (hf s).2 ⟨hs, hm⟩, hl⟩ h
  · exact (Lemmas.changed h).1
  · exact (Lemmas.changed h).1
  · obtain ⟨h1, h2⟩ := Lemmas.changed h
    exact ⟨hE _ _ _ _ h1, fun f hf => hE _ _ _ _ (h2 f hf).2⟩

end Sharing.accessFollowsShares.Proofs
