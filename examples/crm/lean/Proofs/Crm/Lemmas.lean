import FrFlowGen.Crm.Domain

/-! Facts shared by the authored proofs: about a store with the rows about one record replaced (what the
database holds after the write side saves a write), used by WritesTakeEffect and WritesOnlyAsAsked; and
about what users asked (`askedIn`), the history alone, used by StoreMirrorsRequests and the root. -/

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
    | some u =>
      obtain ⟨h2, h3⟩ := h2
      refine ⟨(mem_expiries s t id_ _).2 (Or.inr ⟨h2, rfl⟩), fun e he hpair => ?_⟩
      rw [mem_expiries] at he
      rcases he with ⟨_, hne⟩ | ⟨he, _⟩
      · exact absurd hpair.1 hne
      · exact h3 e he hpair
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

/-- A write that changes nothing it did not ask still does so when only the rows about its record are
stored: the other rows are those of the store before it. -/
theorem onlyAsked_replace (s t : CrmStore) (w : WriteCmd) (h : onlyAsked s w t) :
    onlyAsked s w (replaceAbout s (about w) (aboutRecord t (about w))) := by
  obtain ⟨⟨⟨⟨hRec, hShT⟩, hShS⟩, hExT⟩, hExS⟩ := h
  refine ⟨⟨⟨⟨fun r hr => ?_, fun sh hsh => ?_⟩, fun sh hsh => ?_⟩, fun e he => ?_⟩, fun e he => ?_⟩
  · rw [mem_records] at hr
    rcases hr with ⟨hr, _⟩ | ⟨hr, _⟩
    · exact Or.inl hr
    · exact hRec r hr
  · rw [mem_shares] at hsh
    rcases hsh with ⟨hsh, _⟩ | ⟨hsh, _⟩
    · exact Or.inl hsh
    · exact hShT sh hsh
  · rw [mem_shares]
    by_cases hid : sh.record = about w
    · rcases hShS sh hsh with ht | hc
      · exact Or.inl (Or.inr ⟨ht, hid⟩)
      · exact Or.inr hc
    · exact Or.inl (Or.inl ⟨hsh, hid⟩)
  · rw [mem_expiries] at he
    rcases he with ⟨he, _⟩ | ⟨he, _⟩
    · exact Or.inl he
    · exact hExT e he
  · rw [mem_expiries]
    by_cases hid : e.record = about w
    · rcases hExS e he with ht | hc
      · exact Or.inl (Or.inr ⟨ht, hid⟩)
      · exact Or.inr hc
    · exact Or.inl (Or.inl ⟨he, hid⟩)

/-! What users asked: facts about the history alone, used by StoreMirrorsRequests and the root. -/

/-- What a history and one more event asked: that event, after what the history asked. -/
theorem askedIn_snoc (es : List Event) (e : Event) :
    askedIn (es ++ [e]) = askedStep (askedIn es) e := by
  simp only [askedIn, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- No event takes back a record added. -/
theorem askedStep_records {a : Asked} (e : Event) {r : CrmRecord} (h : r ∈ a.records) :
    r ∈ (askedStep a e).records := by
  cases e with
  | Expired now => simpa [askedStep] using h
  | Wrote w =>
    rcases w with ⟨u, ch⟩
    cases ch with
    | Add x =>
      simp only [askedStep]
      split
      · exact List.mem_append_left _ h
      · exact h
    | ShareWith i to v =>
      simp only [askedStep]
      split
      · exact h
      · exact h
    | Unshare i to =>
      simp only [askedStep]
      split
      · exact h
      · exact h

/-- A record added stays added, whatever is asked after it. -/
theorem askedIn_records_append (pre post : List Event) {r : CrmRecord} (h : r ∈ (askedIn pre).records) :
    r ∈ (askedIn (pre ++ post)).records := by
  simp only [askedIn, List.foldl_append]
  exact FrFlow.always (fun a e => askedStep a e) (fun a => r ∈ a.records) _ h (fun a e ha => askedStep_records e ha) post

/-- What users asked has one record per id, and one share per record and company. -/
theorem askedIn_unique (es : List Event) :
    (∀ x ∈ (askedIn es).records, ∀ y ∈ (askedIn es).records, x.id_ = y.id_ → x = y) ∧
    (∀ g ∈ (askedIn es).grants, ∀ g' ∈ (askedIn es).grants, g.record = g'.record → g.to = g'.to → g = g') := by
  simp only [askedIn]
  apply FrFlow.always (fun a e => askedStep a e)
    (fun a => (∀ x ∈ a.records, ∀ y ∈ a.records, x.id_ = y.id_ → x = y) ∧
      (∀ g ∈ a.grants, ∀ g' ∈ a.grants, g.record = g'.record → g.to = g'.to → g = g'))
  · simp
  · intro a e ⟨hR, hG⟩
    -- a filter of unique shares is unique
    have hFilter : ∀ (p : Grant → Bool), ∀ g ∈ a.grants.filter p, ∀ g' ∈ a.grants.filter p,
        g.record = g'.record → g.to = g'.to → g = g' :=
      fun p g hg g' hg' => hG g (List.mem_filter.1 hg).1 g' (List.mem_filter.1 hg').1
    cases e with
    | Expired now => exact ⟨hR, hFilter _⟩
    | Wrote w =>
      rcases w with ⟨u, ch⟩
      cases ch with
      | Add x =>
        simp only [askedStep]
        split
        · rename_i hc
          refine ⟨fun y hy z hz hyz => ?_, hG⟩
          simp only [List.mem_append, List.mem_singleton] at hy hz
          rcases hy with hy | rfl <;> rcases hz with hz | rfl
          · exact hR y hy z hz hyz
          · exact absurd ⟨y, hy, hyz⟩ hc.2
          · exact absurd ⟨z, hz, hyz.symm⟩ hc.2
          · rfl
        · exact ⟨hR, hG⟩
      | ShareWith i to v =>
        simp only [askedStep]
        split
        · refine ⟨hR, fun g hg g' hg' hr ht => ?_⟩
          simp only [List.mem_append, List.mem_singleton] at hg hg'
          rcases hg with hg | rfl <;> rcases hg' with hg' | rfl
          · exact hFilter _ g hg g' hg' hr ht
          · simp only [List.mem_filter, decide_eq_true_eq] at hg
            exact absurd ⟨hr, ht⟩ hg.2
          · simp only [List.mem_filter, decide_eq_true_eq] at hg'
            exact absurd ⟨hr.symm, ht.symm⟩ hg'.2
          · rfl
        · exact ⟨hR, hG⟩
      | Unshare i to =>
        simp only [askedStep]
        split
        · exact ⟨hR, hFilter _⟩
        · exact ⟨hR, hG⟩

/-- A share of what users asked, other than the one a write replaces, is as it was. -/
theorem grant_filter_other (gs : List Grant) (id0 : Int) (to0 : TenantId) (T id_ : Int) (c : TenantId)
    (hOther : ¬(id_ = id0 ∧ c = to0)) :
    (∃ g ∈ gs.filter (fun g => decide (¬(g.record = id0 ∧ g.to = to0))), (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.until = some t → T < t) ↔
    (∃ g ∈ gs, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.until = some t → T < t) := by
  constructor
  · rintro ⟨g, hg, hPair, hKeep⟩
    exact ⟨g, (List.mem_filter.1 hg).1, hPair, hKeep⟩
  · rintro ⟨g, hg, hPair, hKeep⟩
    refine ⟨g, List.mem_filter.2 ⟨hg, decide_eq_true ?_⟩, hPair, hKeep⟩
    rintro ⟨hRecord, hTo⟩
    exact hOther ⟨hPair.1.symm.trans hRecord, hPair.2.symm.trans hTo⟩

/-- The share a write replaces or ends is no longer among those it keeps. -/
theorem grant_filter_self (gs : List Grant) (id0 : Int) (to0 : TenantId) (T : Int) :
    ¬∃ g ∈ gs.filter (fun g => decide (¬(g.record = id0 ∧ g.to = to0))),
      (g.record = id0 ∧ g.to = to0) ∧ ∀ t, g.until = some t → T < t := by
  rintro ⟨g, hg, hPair, _⟩
  exact (of_decide_eq_true (List.mem_filter.1 hg).2) hPair

/-- A share given anew is not of another record and company. -/
theorem grant_append_other (gs : List Grant) (id0 : Int) (to0 : TenantId) (u : Option Int) (T id_ : Int) (c : TenantId)
    (hOther : ¬(id_ = id0 ∧ c = to0)) :
    (∃ g ∈ gs ++ [Grant.mk id0 to0 u], (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.until = some t → T < t) ↔
    (∃ g ∈ gs, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.until = some t → T < t) := by
  constructor
  · rintro ⟨g, hg, hPair, hKeep⟩
    rcases List.mem_append.1 hg with hg | hg
    · exact ⟨g, hg, hPair, hKeep⟩
    · rw [List.mem_singleton] at hg
      subst hg
      exact absurd ⟨hPair.1.symm, hPair.2.symm⟩ hOther
  · rintro ⟨g, hg, hPair, hKeep⟩
    exact ⟨g, List.mem_append_left _ hg, hPair, hKeep⟩

end Crm.Lemmas
