import FrFlowGen.Sharing.AccessFollowsShares.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of AccessFollowsShares. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.AccessFollowsShares.Proofs
open Sharing.AccessFollowsShares

/-- Who a share must be with, as AccessContract lists them, is whom it reaches (Reach). -/
theorem with_iff (lib : Library) (p : PersonId) (g : Grantee) :
    (g ∈ Grantee.Person p :: List.map (fun t => Grantee.Team t.id_) (List.filter (fun t_1 => decide (p ∈ t_1.members)) lib.teams)) ↔
      (match g with
        | Grantee.Person q => q = p
        | Grantee.Team t => ∃ team, team ∈ lib.teams ∧ team.id_ = t ∧ p ∈ team.members) := by
  cases g with
  | Person q => simp
  | Team t =>
    simp only [List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq, reduceCtorEq, false_or, Grantee.Team.injEq]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, h3⟩; exact ⟨a, h1, h3, h2⟩
    · rintro ⟨a, h1, h3, h2⟩; exact ⟨a, ⟨h1, h2⟩, h3⟩

/-- What a share must be of, as AccessContract lists it, is what covers the document (Cover). -/
theorem of_iff (lib : Library) (d : DocumentId) (t : Target) :
    (t ∈ Target.Doc d :: List.flatMap (fun doc => List.map (fun f => Target.InFolder f) doc.folders)
        (List.filter (fun doc_1 => decide (doc_1.id_ = d)) lib.documents)) ↔
      (match t with
        | Target.Doc d_1 => Target.Doc d = Target.Doc d_1
        | Target.InFolder f => ∃ doc, doc ∈ lib.documents ∧ doc.id_ = d ∧ f ∈ doc.folders) := by
  cases t with
  | Doc e => simp [eq_comm]
  | InFolder f =>
    simp only [List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq, reduceCtorEq, false_or,
      Target.InFolder.injEq]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, b, h3, rfl⟩; exact ⟨a, h1, h2, h3⟩
    · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, ⟨h1, h2⟩, f, h3, rfl⟩

theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  -- Handling is not needed for the purpose: root_impl composes it.
  clear h_HandleContract
  simp only [frflow_defs] at *
  -- The branches give the second half: invitations, the trash and housekeeping each say who may change them.
  obtain ⟨⟨hOffers, hAccept⟩, _⟩ := h_InvitationsAreOffers
  obtain ⟨hTrash, _⟩ := h_TrashUntilGone
  obtain ⟨hTidy, _⟩ := h_HousekeepingClearsOnlyTheEnded
  refine ⟨⟨⟨⟨⟨⟨⟨fun lib t p d => ?_, fun lib t by_ s h => ?_⟩, fun lib t by_ what withWhom h => ?_⟩,
    fun lib t by_ d into h => ?_⟩,
    fun lib t by_ to what => ⟨(hOffers lib t by_ to what).1, fun level => ((hOffers lib t by_ to what).2 level).1⟩⟩,
    hAccept⟩, fun lib t by_ d => ⟨(hTrash lib t by_ d).1, fun h => ((hTrash lib t by_ d).2 h).1⟩⟩, hTidy⟩
  · -- Access: the shares AccessContract keeps are those in force that reach the person and cover the document; and
    -- a document in the trash gives no access.
    have hf : ∀ s, s ∈ List.filter (fun s => decide ((inForce s t ∧ s.withWhom ∈ Grantee.Person p :: List.map
        (fun t => Grantee.Team t.id_) (List.filter (fun t_1 => decide (p ∈ t_1.members)) lib.teams)) ∧
        s.what ∈ Target.Doc d :: List.flatMap (fun doc => List.map (fun f => Target.InFolder f) doc.folders)
        (List.filter (fun doc_1 => decide (doc_1.id_ = d)) lib.documents))) lib.shares ↔ s ∈ lib.shares ∧
          ((inForce s t ∧ (match s.withWhom with
            | Grantee.Person q => q = p
            | Grantee.Team t => ∃ team, team ∈ lib.teams ∧ team.id_ = t ∧ p ∈ team.members)) ∧
          match s.what with
            | Target.Doc d_1 => Target.Doc d = Target.Doc d_1
            | Target.InFolder f => ∃ doc, doc ∈ lib.documents ∧ doc.id_ = d ∧ f ∈ doc.folders) := by
      intro s; rw [List.mem_filter, decide_eq_true_eq, with_iff, of_iff]
    rw [h_CanViewContract, h_CanEditContract, h_AccessContract]
    by_cases ht : ∃ doc, doc ∈ lib.documents ∧ doc.id_ = d ∧ doc.trashed ≠ none
    · simp [ht]
    · simp only [ht, ite_false, not_false_eq_true, true_and]
      constructor
      · apply propext
        split
        · next h => obtain ⟨s, hs, _⟩ := h; exact ⟨fun _ => ⟨s, (hf s).1 hs⟩, fun _ => nofun⟩
        · split
          · next _ he => simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
                         intro s hs hw hc; exact List.eq_nil_iff_forall_not_mem.mp he s ((hf s).2 ⟨hs, hw, hc⟩)
          · next _ he => obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ he
                         exact ⟨fun _ => ⟨s, (hf s).1 hs⟩, fun _ => nofun⟩
      · apply propext
        split
        · next h => obtain ⟨s, hs, hl⟩ := h
                    exact ⟨fun _ => ⟨s, (hf s).1 hs |>.1, (hf s).1 hs |>.2, hl⟩, fun _ => rfl⟩
        · next h => constructor
                    · intro he; split at he <;> simp at he
                    · rintro ⟨s, hs, hm, hl⟩; exact absurd ⟨s, (hf s).2 ⟨hs, hm⟩, hl⟩ h
  · rw [h_ShareContract] at h; exact Sharing.Lemmas.changed h
  · rw [h_UnshareContract] at h; exact Sharing.Lemmas.changed h
  · rw [h_MoveContract] at h
    obtain ⟨h1, h2⟩ := Sharing.Lemmas.changed h
    refine ⟨h1, ?_⟩
    cases into with
    | none => trivial
    | some f => exact h2.2

end Sharing.AccessFollowsShares.Proofs
