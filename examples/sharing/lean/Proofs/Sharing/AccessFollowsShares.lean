import FrFlowGen.Sharing.AccessFollowsShares.Spec

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

/-- A change made by an `if` whose other branch changes nothing: its condition held. -/
theorem changed {α : Type} {c : Prop} {inst : Decidable c} {a b : α} (h : @ite α c inst a b ≠ b) : c :=
  Classical.byContradiction fun hn => h (ite_eq_right hn)

/-- What reads a value the same on both branches of an `if` reads it the same on the `if`. -/
theorem ite_same {α β : Type} {c : Prop} {inst : Decidable c} (f : α → β) (a b : α) (h : f a = f b) :
    f (@ite α c inst a b) = f b := by
  split
  · exact h
  · rfl

theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  -- The deadlines and the handling are parts the purpose does not need: it holds whatever the lifetimes are.
  clear h_ExpiredSharesGiveNoAccess h_InvitationsAcceptedInTime h_TrashPurgedOnTime h_InvitationsLapseOnTime
    h_EndedStaysEnded h_HandleContract
  -- Housekeeping removes only what has ended (TidyContract), before the words are unfolded.
  have tidyKeeps : ∀ lib t,
      (∀ s ∈ lib.shares, (s ∈ (tidy lib t).shares ∨ ¬inForce s t) ∨ Sharing.Housekeeping.ofGone gone lib t s) ∧
      (∀ i ∈ lib.invitations, i ∈ (tidy lib t).invitations ∨ ¬isOpen i t) ∧
      (∀ doc ∈ lib.documents, doc ∈ (tidy lib t).documents ∨ gone doc t) := by
    intro lib t
    have h := h_TidyContract lib t
    simp only [Sharing.TidyContract.post] at h
    rw [h]
    refine ⟨fun s hs => ?_, fun i hi => ?_, fun doc hd => ?_⟩
    · by_cases hg : Sharing.Housekeeping.ofGone gone lib t s
      · exact Or.inr hg
      · by_cases hf : inForce s t
        · exact Or.inl (Or.inl (List.mem_filter.mpr ⟨hs, decide_eq_true ⟨hf, hg⟩⟩))
        · exact Or.inl (Or.inr hf)
    · by_cases ho : isOpen i t
      · exact Or.inl (List.mem_filter.mpr ⟨hi, decide_eq_true ho⟩)
      · exact Or.inr ho
    · by_cases hg : gone doc t
      · exact Or.inr hg
      · exact Or.inl (List.mem_filter.mpr ⟨hd, decide_eq_true hg⟩)
  simp only [frflow_defs] at *
  refine ⟨⟨⟨⟨⟨⟨⟨⟨fun lib t p d => ?_, fun lib t by_ s h => ?_⟩, fun lib t by_ what withWhom h => ?_⟩,
    fun lib t by_ d into h => ?_⟩, fun lib t by_ d => ⟨fun h => ?_, fun h => ?_⟩⟩,
    fun lib t by_ to what => ⟨fun h => ?_, fun level => ⟨fun h => ?_, fun p d => ?_⟩⟩⟩,
    fun lib t p what h => ?_⟩, fun lib t => ⟨⟨fun s hs => ?_, fun i hi => ?_⟩, fun doc hd => ?_⟩⟩,
    ⟨⟨fun s t h => ?_, fun i => ?_⟩, fun doc t h => ?_⟩⟩
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
  · rw [h_ShareContract] at h; exact changed h
  · rw [h_UnshareContract] at h; exact changed h
  · rw [h_MoveContract] at h
    obtain ⟨h1, h2⟩ := changed h
    refine ⟨h1, ?_⟩
    cases into with
    | none => trivial
    | some f => exact h2.2
  · rw [h_TrashContract] at h; exact changed h
  · rw [h_RestoreContract] at h; exact changed h
  · rw [h_WithdrawContract] at h; exact changed h
  · rw [h_InviteContract] at h; exact changed h
  · -- An invitation changes only the invitations, which access does not read.
    have key : ∀ X, access { lib with invitations := X } t p d = access lib t p d := by
      intro X; rw [h_AccessContract, h_AccessContract]; rfl
    rw [h_InviteContract]
    exact ite_same (fun L => access L t p d) _ _ (key _)
  · rw [h_AcceptContract] at h
    split at h
    · next i heq => exact ⟨i, List.mem_of_find?_eq_some heq, by simpa using List.find?_some heq⟩
    · exact absurd rfl h
  · exact (tidyKeeps lib t).1 s hs
  · exact (tidyKeeps lib t).2.1 i hi
  · exact (tidyKeeps lib t).2.2 doc hd
  · -- What the purpose asks of the lifetimes, from their contracts.
    have hn : s.«until» = none := by simpa using h
    rw [h_InForceContract, hn]; trivial
  · rw [h_IsOpenContract]; first | omega | (simp only [Sharing.invitationLasts]; omega)
  · have hn : doc.trashed = none := by simpa using h
    rw [h_GoneContract, hn]; simp

end Sharing.AccessFollowsShares.Proofs
