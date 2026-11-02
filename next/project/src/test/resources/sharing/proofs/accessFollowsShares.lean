import FrFlowGen.Sharing.accessFollowsShares.Spec
import Proofs.Sharing.Lemmas

/-! Access, as accessContract works it out, is what the words say: the shares it keeps are those in force that reach
the person (reach) and cover the document (cover), and a document in the trash gives no access (inTrash). The
branches give the second half: invitations, the trash, housekeeping, access requests and ownership each say who may
change them; sharing, unsharing and moving say so of themselves (their contracts' code). -/

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
  intro access reaches covers ownedBy isPending events startedAt reminderDue inForce handle announce record
    hReach hCover _ _ hTrash _ hOffers hTrashGone hTidy hAsks _ _ _ hAccess _ _ _ _ _ _
  obtain ⟨⟨hOffers, hAccept⟩, _⟩ := hOffers
  obtain ⟨hTrashed, _⟩ := hTrashGone
  obtain ⟨hTidy, _⟩ := hTidy
  obtain ⟨⟨hAsk, hAnswer⟩, _⟩ := hAsks
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨fun lib t p d => ?_, fun lib t by_ s h => ?_⟩, fun lib t by_ what withWhom h => ?_⟩,
    fun lib t by_ d into h => ?_⟩,
    fun lib t by_ to what => ⟨(hOffers lib t by_ to what).1, fun level => ((hOffers lib t by_ to what).2 level).1⟩⟩,
    hAccept⟩, fun lib t by_ d => ⟨(hTrashed lib t by_ d).1, fun h => ((hTrashed lib t by_ d).2 h).1⟩⟩, hAsk⟩,
    fun lib t by_ p d => ⟨fun h => ((hAnswer lib t by_ p d).1 h).1, (hAnswer lib t by_ p d).2⟩⟩,
    fun lib t by_ d to h => (Lemmas.changed h).1.2⟩, hTidy⟩
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
    simp only [canViewCode, canEditCode, mayViewCode, mayEditCode, inTrashCode, hA]
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
    exact ⟨h1, fun f hf => (h2 f hf).2⟩

end Sharing.accessFollowsShares.Proofs
