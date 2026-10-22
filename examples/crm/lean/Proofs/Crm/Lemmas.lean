import FrFlowGen.Crm.Domain

/-! Facts about a store with the rows about one record replaced (what the database holds after the
write side saves a write), shared by the proofs of WritesTakeEffect, WritesInCompany and
StoreConsistent. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.Lemmas
open Crm

/-- A record is in the replaced store when it is in the old one under another id, or among the new rows. -/
theorem mem_records (s t : CrmStore) (id_ : Int) (r : CrmRecord) :
    r ∈ (replaceAbout s id_ (aboutRecord t id_)).records ↔ (r ∈ s.records ∧ r.id_ ≠ id_) ∨ (r ∈ t.records ∧ r.id_ = id_) := by
  simp [replaceAbout, aboutRecord]

theorem mem_shares (s t : CrmStore) (id_ : Int) (sh : Share) :
    sh ∈ (replaceAbout s id_ (aboutRecord t id_)).shares ↔ (sh ∈ s.shares ∧ sh.record ≠ id_) ∨ (sh ∈ t.shares ∧ sh.record = id_) := by
  simp [replaceAbout, aboutRecord]

theorem mem_expiries (s t : CrmStore) (id_ : Int) (e : Expiry) :
    e ∈ (replaceAbout s id_ (aboutRecord t id_)).expiries ↔ (e ∈ s.expiries ∧ e.record ≠ id_) ∨ (e ∈ t.expiries ∧ e.record = id_) := by
  simp [replaceAbout, aboutRecord]

/-- Replacing the rows about one record by those of a store with unique ids keeps ids unique: the
records kept have other ids than the new ones. -/
theorem idsUnique_replace (s t : CrmStore) (id_ : Int) (hs : idsUnique s) (ht : idsUnique t) :
    idsUnique (replaceAbout s id_ (aboutRecord t id_)) := by
  unfold idsUnique at *
  intro a ha b hb hab
  rw [mem_records] at ha hb
  rcases ha with ⟨ha, hai⟩ | ⟨ha, hai⟩ <;> rcases hb with ⟨hb, hbi⟩ | ⟨hb, hbi⟩
  · exact hs a ha b hb hab
  · exact absurd (hab.trans hbi) hai
  · exact absurd (hab.symm.trans hai) hbi
  · exact ht a ha b hb hab

/-- What a write asks is about its own record's rows only: it holds of the replaced store when it holds
of the store the write led to. -/
theorem takesEffect_replace (s t : CrmStore) (w : WriteCmd) (h : takesEffect s w t) :
    takesEffect s w (replaceAbout s (about w) (aboutRecord t (about w))) := by
  rcases w with ⟨a, ch⟩
  cases ch with
  | Add r =>
    simp only [takesEffect, about] at h ⊢
    intro hc
    rw [mem_records]
    exact Or.inr ⟨h hc, rfl⟩
  | ShareWith id_ to u =>
    simp only [takesEffect, about] at h ⊢
    intro hc
    obtain ⟨h1, h2⟩ := h hc
    refine ⟨(mem_shares s t id_ _).2 (Or.inr ⟨h1, rfl⟩), ?_⟩
    cases u with
    | some u => exact (mem_expiries s t id_ _).2 (Or.inr ⟨h2, rfl⟩)
    | none =>
      rintro ⟨e, he, her, het⟩
      rw [mem_expiries] at he
      rcases he with ⟨_, hne⟩ | ⟨he, _⟩
      · exact hne her
      · exact h2 ⟨e, he, her, het⟩
  | Unshare id_ to =>
    simp only [takesEffect, about] at h ⊢
    intro hc hm
    rw [mem_shares] at hm
    rcases hm with ⟨_, hne⟩ | ⟨hm, _⟩
    · exact hne rfl
    · exact h hc hm

/-- A company other than the author's holds its records alike in the replaced store, when the write
left its records, and their shares and expiries, as they were. -/
theorem holdsAlike_replace (s t : CrmStore) (id_ : Int) (a c : TenantId) (hc : c ≠ a)
    (hrec : List.filter (fun r => decide (r.tenant ≠ a)) t.records = List.filter (fun r => decide (r.tenant ≠ a)) s.records)
    (hrows : ∀ r ∈ s.records, r.tenant ≠ a → rowsAlike s t r.id_) :
    holdsAlike s (replaceAbout s id_ (aboutRecord t id_)) c := by
  have toT : ∀ r ∈ s.records, r.tenant ≠ a → r ∈ t.records := by
    intro r hr hra
    have : r ∈ List.filter (fun r => decide (r.tenant ≠ a)) s.records := List.mem_filter.2 ⟨hr, by simpa using hra⟩
    rw [← hrec] at this
    exact (List.mem_filter.1 this).1
  have toS : ∀ r ∈ t.records, r.tenant ≠ a → r ∈ s.records := by
    intro r hr hra
    have : r ∈ List.filter (fun r => decide (r.tenant ≠ a)) t.records := List.mem_filter.2 ⟨hr, by simpa using hra⟩
    rw [hrec] at this
    exact (List.mem_filter.1 this).1
  unfold holdsAlike
  refine ⟨fun r hr hrc => ?_, fun r hr hrc => ?_⟩
  · have hra : r.tenant ≠ a := hrc ▸ hc
    refine ⟨(mem_records s t id_ r).2 ?_, ?_⟩
    · by_cases hid : r.id_ = id_
      · exact Or.inr ⟨toT r hr hra, hid⟩
      · exact Or.inl ⟨hr, hid⟩
    · have hr2 := hrows r hr hra
      unfold rowsAlike at hr2 ⊢
      obtain ⟨⟨⟨s1, s2⟩, e1⟩, e2⟩ := hr2
      by_cases hid : r.id_ = id_
      · refine ⟨⟨⟨fun sh hsh hshr => (mem_shares s t id_ sh).2 (Or.inr ⟨s1 sh hsh hshr, hshr.trans hid⟩), ?_⟩,
          fun e he her => (mem_expiries s t id_ e).2 (Or.inr ⟨e1 e he her, her.trans hid⟩)⟩, ?_⟩
        · intro sh hsh hshr
          rw [mem_shares] at hsh
          rcases hsh with ⟨hsh, _⟩ | ⟨hsh, _⟩
          · exact hsh
          · exact s2 sh hsh hshr
        · intro e he her
          rw [mem_expiries] at he
          rcases he with ⟨he, _⟩ | ⟨he, _⟩
          · exact he
          · exact e2 e he her
      · refine ⟨⟨⟨fun sh hsh hshr => (mem_shares s t id_ sh).2 (Or.inl ⟨hsh, fun h => hid (hshr.symm.trans h)⟩), ?_⟩,
          fun e he her => (mem_expiries s t id_ e).2 (Or.inl ⟨he, fun h => hid (her.symm.trans h)⟩)⟩, ?_⟩
        · intro sh hsh hshr
          rw [mem_shares] at hsh
          rcases hsh with ⟨hsh, _⟩ | ⟨_, hshi⟩
          · exact hsh
          · exact absurd (hshr.symm.trans hshi) hid
        · intro e he her
          rw [mem_expiries] at he
          rcases he with ⟨he, _⟩ | ⟨_, hei⟩
          · exact he
          · exact absurd (her.symm.trans hei) hid
  · have hra : r.tenant ≠ a := hrc ▸ hc
    rw [mem_records] at hr
    rcases hr with ⟨hr, _⟩ | ⟨hr, _⟩
    · exact hr
    · exact toS r hr hra

end Crm.Lemmas
