import FrFlowGen.Crm.Domain

/-! Facts shared by crm's proofs (today's `Lemmas`, over the port's names): about a store with the rows about one
record replaced (what the database holds after the write side saves a write), used by `writesTakeEffect` and
`writesOnlyAsAsked`; about one row per key, which a write keeps (`made_write`); and about what users asked
(`askedIn`), the history alone, used by the roots. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.Lemmas
open Crm

/-- A record is in the replaced store when it is in the old one under another id, or among the new rows. -/
theorem mem_records (s t : CrmStore) (id_ : Int) (r : CrmRecord) :
    r ∈ (replaceAbout s id_ (aboutRecord t id_)).records ↔
      (r ∈ s.records ∧ r.id_ ≠ id_) ∨ (r ∈ t.records ∧ r.id_ = id_) := by
  simp [replaceAbout, aboutRecord]

theorem mem_shares (s t : CrmStore) (id_ : Int) (sh : Share) :
    sh ∈ (replaceAbout s id_ (aboutRecord t id_)).shares ↔
      (sh ∈ s.shares ∧ sh.record ≠ id_) ∨ (sh ∈ t.shares ∧ sh.record = id_) := by
  simp [replaceAbout, aboutRecord]

theorem mem_expiries (s t : CrmStore) (id_ : Int) (e : Expiry) :
    e ∈ (replaceAbout s id_ (aboutRecord t id_)).expiries ↔
      (e ∈ s.expiries ∧ e.record ≠ id_) ∨ (e ∈ t.expiries ∧ e.record = id_) := by
  simp [replaceAbout, aboutRecord]

/-- What a write asks is about its own record's rows only: it holds of the replaced store when it holds of the
store the write led to. -/
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

/-- A write that changes nothing it did not ask still does so when only the rows about its record are stored: the
other rows are those of the store before it. -/
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

/-! One row per key: a list with one row per key keeps it when filtered, and when a row of a key it no longer
holds is added. -/

theorem pairwise_filter {α : Type} (R : α → α → Prop) (p : α → Bool) (xs : List α) (h : xs.Pairwise R) :
    (xs.filter p).Pairwise R :=
  List.Pairwise.sublist (List.filter_sublist) h

theorem pairwise_snoc {α : Type} (R : α → α → Prop) (xs : List α) (y : α) (h : xs.Pairwise R)
    (hy : ∀ x ∈ xs, R x y) : (xs ++ [y]).Pairwise R := by
  rw [List.pairwise_append]
  exact ⟨h, List.pairwise_singleton R y, fun x hx z hz => by rw [List.mem_singleton] at hz; exact hz ▸ hy x hx⟩

/-- Rows of other keys, then rows of one key with one row per key, have one row per key. -/
theorem pairwise_replace {α : Type} (R : α → α → Prop) (xs ys : List α) (f : α → Int) (i : Int)
    (hxs : xs.Pairwise R) (hys : ys.Pairwise R) (hk : ∀ x y, f x ≠ f y → R x y) (hys_i : ∀ y ∈ ys, f y = i) :
    (xs.filter (fun x => decide (¬(f x = i))) ++ ys).Pairwise R := by
  rw [List.pairwise_append]
  refine ⟨pairwise_filter R _ xs hxs, hys, fun x hx y hy => hk x y ?_⟩
  have := of_decide_eq_true (List.mem_filter.1 hx).2
  rw [hys_i y hy]
  exact this

/-- A write keeps one row per key: an add only under an id no record has, a share or unshare replacing the one
share, and the one time, of its record with its company. -/
theorem applyWrite_onePerKey (s : CrmStore) (w : WriteCmd) (h : onePerKey s) : onePerKey (applyWrite s w) := by
  obtain ⟨⟨hr, hs⟩, he⟩ := h
  rcases w with ⟨a, ch⟩
  cases ch with
  | Add r =>
    simp only [applyWrite]
    split
    · rename_i hAllowed
      refine ⟨⟨pairwise_snoc _ _ _ hr (fun x hx hxr => hAllowed.2 ⟨x, hx, hxr⟩), hs⟩, he⟩
    · exact ⟨⟨hr, hs⟩, he⟩
  | ShareWith id_ to u =>
    simp only [applyWrite]
    split
    · refine ⟨⟨hr, pairwise_snoc _ _ _ (pairwise_filter _ _ _ hs) (fun x hx hxe => ?_)⟩, ?_⟩
      · exact of_decide_eq_true (List.mem_filter.1 hx).2 hxe
      · cases u with
        | none => simpa using pairwise_filter _ _ _ he
        | some u =>
          refine pairwise_snoc _ _ _ (pairwise_filter _ _ _ he) (fun x hx hxe => ?_)
          exact of_decide_eq_true (List.mem_filter.1 hx).2 hxe
    · exact ⟨⟨hr, hs⟩, he⟩
  | Unshare id_ to =>
    simp only [applyWrite]
    split
    · exact ⟨⟨hr, pairwise_filter _ _ _ hs⟩, pairwise_filter _ _ _ he⟩
    · exact ⟨⟨hr, hs⟩, he⟩

/-- What a store with one row per key holds about one record has one row per key. -/
theorem aboutRecord_onePerKey (t : CrmStore) (i : Int) (h : onePerKey t) : onePerKey (aboutRecord t i) := by
  obtain ⟨⟨hr, hs⟩, he⟩ := h
  exact ⟨⟨pairwise_filter _ _ _ hr, pairwise_filter _ _ _ hs⟩, pairwise_filter _ _ _ he⟩

/-- A store with one row per key, the rows about a record replaced by another's with one row per key: one row per
key. -/
theorem replace_onePerKey (st t : CrmStore) (i : Int) (hst : onePerKey st) (ht : onePerKey t) :
    onePerKey (replaceAbout st i (aboutRecord t i)) := by
  obtain ⟨⟨hr, hs⟩, he⟩ := hst
  obtain ⟨⟨tr, ts⟩, te⟩ := ht
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact pairwise_replace _ _ _ (fun r => r.id_) i hr (pairwise_filter _ _ _ tr) (fun x y hxy hid => hxy hid)
      (fun y hy => of_decide_eq_true (List.mem_filter.1 hy).2)
  · exact pairwise_replace _ _ _ (fun sh => sh.record) i hs (pairwise_filter _ _ _ ts)
      (fun x y hxy he => hxy (congrArg Share.record he)) (fun y hy => of_decide_eq_true (List.mem_filter.1 hy).2)
  · exact pairwise_replace _ _ _ (fun e => e.record) i he (pairwise_filter _ _ _ te)
      (fun x y hxy he => hxy he.1) (fun y hy => of_decide_eq_true (List.mem_filter.1 hy).2)

/-- A run of the expiry job keeps one row per key: the same records, and some of the shares and expiries. -/
theorem endsDueAt_onePerKey (s : CrmStore) (now : Int) (t : CrmStore) (h : endsDueAt s now t)
    (hs : onePerKey s) : onePerKey t := by
  obtain ⟨⟨hr, hsh⟩, he⟩ := h
  obtain ⟨⟨a, b⟩, c⟩ := hs
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hr]; exact a
  · rw [hsh]; exact pairwise_filter _ _ _ b
  · rw [he]; exact pairwise_filter _ _ _ c

/-! The expiry job's loop on the database's model: what it stores, record by record. -/

/-- One field of a store after a record's rows are stored, as `aboutRecord` reads it. -/
theorem filter_replace {α : Type} (f : α → Int) (xs ys : List α) (i j : Int) :
    List.filter (fun x => decide (f x = j))
        (List.filter (fun x => decide (¬(f x = i))) xs ++ List.filter (fun x => decide (f x = i)) ys) =
      if j = i then List.filter (fun x => decide (f x = j)) ys else List.filter (fun x => decide (f x = j)) xs := by
  rw [List.filter_append, List.filter_filter, List.filter_filter]
  split
  · rename_i h
    subst h
    rw [List.filter_eq_nil_iff.mpr (fun x _ => by
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; exact fun h1 h2 => h2 h1), List.nil_append]
    apply List.filter_congr; intro x _; by_cases hx : f x = j <;> simp [hx]
  · rename_i h
    have hy : List.filter (fun a => decide (f a = j) && decide (f a = i)) ys = [] :=
      List.filter_eq_nil_iff.mpr (fun x _ => by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; exact fun h1 h2 => h (h1 ▸ h2))
    rw [hy, List.append_nil]
    apply List.filter_congr; intro x _; by_cases hx : f x = j <;> simp [hx]; omega

/-- A record's rows after another record's (or its own) rows are stored. -/
theorem about_replace (st t : CrmStore) (i j : Int) :
    aboutRecord (replaceAbout st i (aboutRecord t i)) j = if j = i then aboutRecord t j else aboutRecord st j := by
  have hr := filter_replace (fun r : CrmRecord => r.id_) st.records t.records i j
  have hs := filter_replace (fun sh : Share => sh.record) st.shares t.shares i j
  have he := filter_replace (fun e : Expiry => e.record) st.expiries t.expiries i j
  simp only [aboutRecord, replaceAbout] at hr hs he ⊢
  split <;> simp_all

/-- After storing the new store's rows about each record of `ids` whose rows differ (`c`). -/
theorem about_stored (ids : List Int) (c : Int → Prop) {d : ∀ i, Decidable (c i)} (s t : CrmStore) (j : Int) :
    aboutRecord (ids.foldl (fun st i => @ite _ (c i) (d i) (replaceAbout st i (aboutRecord t i)) st) s) j =
      if j ∈ ids ∧ c j then aboutRecord t j else aboutRecord s j := by
  induction ids generalizing s with
  | nil => simp
  | cons i ids ih =>
    rw [List.foldl_cons, ih]
    by_cases hc : c i
    · rw [ite_eq_left hc, about_replace]
      by_cases h1 : j ∈ ids <;> by_cases h2 : j = i <;> by_cases h3 : c j <;> simp_all
    · rw [ite_eq_right hc]
      by_cases h1 : j ∈ ids <;> by_cases h2 : j = i <;> by_cases h3 : c j <;> simp_all

/-- A store says nothing about a record it does not mention. -/
theorem about_absent (s : CrmStore) (j : Int) (h : j ∉ idsIn s) : aboutRecord s j = ⟨[], [], []⟩ := by
  simp only [idsIn, List.mem_append, List.mem_map, not_or, not_exists, not_and] at h
  obtain ⟨⟨hr, hs⟩, he⟩ := h
  simp only [aboutRecord, CrmStore.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> rw [List.filter_eq_nil_iff] <;> intro x hx <;> simp only [decide_eq_true_eq]
  · exact fun e => hr x hx e
  · exact fun e => hs x hx e
  · exact fun e => he x hx e

/-- A loop whose every step yields, each step's world given by `step`: the world goes through each in turn. -/
theorem loop (ids : List Int) (f : Int → PUnit → StateM World (ForInStep PUnit)) (step : World → Int → World)
    (hf : ∀ i w, FrFlow.runOn (f i PUnit.unit) w = (ForInStep.yield PUnit.unit, step w i)) (w : World) :
    FrFlow.runOn (forIn ids PUnit.unit f) w = (PUnit.unit, ids.foldl step w) := by
  induction ids generalizing w with
  | nil => rfl
  | cons i ids ih => rw [FrFlow.runOn_forIn_cons, hf i w]; exact ih _

/-- The loop's worlds, by the database's store: its events kept. -/
theorem fold_world (ids : List Int) (c : Int → Prop) {d : ∀ i, Decidable (c i)} (t : CrmStore) (w : World) :
    ids.foldl (fun (x : World) i => @ite _ (c i) (d i) (World.mk (Tables.mk (replaceAbout x.databaseModel.store i
      (aboutRecord t i)) x.databaseModel.events)) x) w =
      World.mk (Tables.mk (ids.foldl (fun st i => @ite _ (c i) (d i) (replaceAbout st i (aboutRecord t i)) st)
        w.databaseModel.store) w.databaseModel.events) := by
  induction ids generalizing w with
  | nil => rfl
  | cons i ids ih =>
    rw [List.foldl_cons, ih, List.foldl_cons]
    by_cases hc : c i
    · simp only [ite_eq_left hc]
    · simp only [ite_eq_right hc]

/-- A store with one row per key, each record's rows replaced by another's with one row per key in turn: one row
per key. -/
theorem stored_onePerKey (ids : List Int) (c : Int → Prop) {d : ∀ i, Decidable (c i)} (st t : CrmStore)
    (hst : onePerKey st) (ht : onePerKey t) :
    onePerKey (ids.foldl (fun st i => @ite _ (c i) (d i) (replaceAbout st i (aboutRecord t i)) st) st) := by
  induction ids generalizing st with
  | nil => exact hst
  | cons i ids ih =>
    rw [List.foldl_cons]
    apply ih
    by_cases hc : c i
    · rw [ite_eq_left hc]; exact replace_onePerKey st t i hst ht
    · rw [ite_eq_right hc]; exact hst

/-! What users asked: facts about the history alone, used by the roots. -/

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
  exact FrFlow.always (fun a e => askedStep a e) (fun a => r ∈ a.records) _ h
    (fun a e ha => askedStep_records e ha) post

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
    (∃ g ∈ gs.filter (fun g => decide (¬(g.record = id0 ∧ g.to = to0))),
      (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.«until» = some t → T < t) ↔
    (∃ g ∈ gs, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.«until» = some t → T < t) := by
  constructor
  · rintro ⟨g, hg, hPair, hKeep⟩
    exact ⟨g, (List.mem_filter.1 hg).1, hPair, hKeep⟩
  · rintro ⟨g, hg, hPair, hKeep⟩
    refine ⟨g, List.mem_filter.2 ⟨hg, decide_eq_true ?_⟩, hPair, hKeep⟩
    rintro ⟨hRecord, hTo⟩
    exact hOther ⟨hPair.1.symm.trans hRecord, hPair.2.symm.trans hTo⟩

/-- A share given anew is not of another record and company. -/
theorem grant_append_other (gs : List Grant) (id0 : Int) (to0 : TenantId) (u : Option Int) (T id_ : Int)
    (c : TenantId) (hOther : ¬(id_ = id0 ∧ c = to0)) :
    (∃ g ∈ gs ++ [Grant.mk id0 to0 u], (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.«until» = some t → T < t) ↔
    (∃ g ∈ gs, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.«until» = some t → T < t) := by
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
