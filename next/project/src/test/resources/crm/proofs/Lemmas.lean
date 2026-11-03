import FrFlowGen.Crm.Domain
import FrFlowGen.Crm.writeContract.Spec
import FrFlowGen.Crm.recordsByQuery.Spec
import FrFlowGen.Crm.searchKeeps.Spec
import FrFlowGen.Crm.sharesExpire.Spec
import FrFlowGen.Crm.readContract.Spec
import FrFlowGen.Crm.dealSearch.Spec
import FrFlowGen.Crm.visibility.Spec
import FrFlowGen.Crm.storeMirrorsRequests.Spec
import FrFlowGen.Crm.recordsKept.Spec
import FrFlowGen.Crm.writesOnlyAsAsked.Spec
import FrFlowGen.Crm.writesTakeEffect.Spec

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

/-- What a store holds about a record, read about that record again, is the same. -/
theorem aboutRecord_idem (t : CrmStore) (i : Int) : aboutRecord (aboutRecord t i) i = aboutRecord t i := by
  simp only [aboutRecord, List.filter_filter, Bool.and_self]

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

/-- The loop's worlds, by the database's store: its events and the clock kept. -/
theorem fold_world (ids : List Int) (c : Int → Prop) {d : ∀ i, Decidable (c i)} (t : CrmStore) (w : World) :
    ids.foldl (fun (x : World) i => @ite _ (c i) (d i)
      { x with databaseModel := Tables.mk (replaceAbout x.databaseModel.store i (aboutRecord t i)) x.databaseModel.events }
      x) w =
      { w with databaseModel := Tables.mk (ids.foldl (fun st i => @ite _ (c i) (d i) (replaceAbout st i (aboutRecord t i)) st) w.databaseModel.store) w.databaseModel.events } := by
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

/-- A store that is the one before changes nothing it was not asked. -/
theorem onlyAsked_self (s : CrmStore) (w : WriteCmd) : onlyAsked s w s := by
  simp only [onlyAsked]
  exact ⟨⟨⟨⟨fun _ h => Or.inl h, fun _ h => Or.inl h⟩, fun _ h => Or.inl h⟩, fun _ h => Or.inl h⟩, fun _ h => Or.inl h⟩

/-- A write that returns the store as it was meets the contract when its author's company may not make it. -/
theorem kept (s : CrmStore) (w : WriteCmd) (hNot : ¬ takesEffect s w s → False) :
    (((∀ r ∈ s.records, r ∈ s.records) ∧ (List.filter (fun r => decide (¬(r.tenant = w.«by».tenant))) s.records) =
      (List.filter (fun r => decide (¬(r.tenant = w.«by».tenant))) s.records)) ∧ takesEffect s w s) ∧
      onlyAsked s w s :=
  ⟨⟨⟨fun _ h => h, rfl⟩, Classical.byContradiction hNot⟩, onlyAsked_self s w⟩

/-- `applyWrite` meets writeContract: what `writeContract`'s `impl` and a `feasible` proof take. -/
theorem applyWrite_contract : writeContract.claim applyWrite := by
  unfold writeContract.claim
  intro s _ _ w
  rcases w with ⟨a, ch⟩
  cases ch with
  | Add r =>
    by_cases hAllowed : r.tenant = a.tenant ∧ ¬∃ x ∈ s.records, x.id_ = r.id_
    · simp only [applyWrite, takesEffect, onlyAsked, addsRecord, changesShare]
      rw [ite_eq_left hAllowed]
      refine ⟨⟨⟨fun x hx => List.mem_append_left _ hx, ?_⟩, fun _ => by simp⟩,
        ⟨⟨⟨⟨fun x hx => ?_, fun _ h => Or.inl h⟩, fun _ h => Or.inl h⟩, fun _ h => Or.inl h⟩, fun _ h => Or.inl h⟩⟩
      · simp [List.filter_append, hAllowed.1]
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inl hx
        · exact Or.inr ⟨⟨rfl, hAllowed.1⟩, hAllowed.2⟩
    · simp only [applyWrite]
      rw [ite_eq_right hAllowed]
      exact kept s _ (fun h => h (fun hc => absurd hc hAllowed))
  | ShareWith id_ to u =>
    by_cases hAllowed : ownRecord s ⟨a, Change.ShareWith id_ to u⟩ id_
    · have hChanges : ∀ (i : Int) (c : TenantId), i = id_ → c = to →
          changesShare s ⟨a, Change.ShareWith id_ to u⟩ i c := by
        intro i c hi hc
        subst hi hc
        simp only [changesShare]
        exact ⟨⟨trivial, trivial⟩, hAllowed⟩
      simp only [applyWrite, takesEffect, onlyAsked, addsRecord]
      rw [ite_eq_left hAllowed]
      refine ⟨⟨⟨fun _ h => h, by simp⟩, fun _ => ⟨by simp, ?_⟩⟩,
        ⟨⟨⟨⟨fun _ h => Or.inl h, fun sh hsh => ?_⟩, fun sh hsh => ?_⟩, fun e he => ?_⟩, fun e he => ?_⟩⟩
      · cases u with
        | some u =>
          refine ⟨by simp, fun e he hPair => ?_⟩
          simp only [List.mem_append, List.mem_filter, List.mem_singleton, decide_eq_true_eq] at he
          rcases he with ⟨_, hNotPair⟩ | rfl
          · exact absurd hPair hNotPair
          · rfl
        | none =>
          simp only [List.append_nil, List.mem_filter, decide_eq_true_eq]
          rintro ⟨e, ⟨_, hNotPair⟩, hRecord, hTo⟩
          exact hNotPair ⟨hRecord, hTo⟩
      · simp only [List.mem_append, List.mem_filter, List.mem_singleton, decide_eq_true_eq] at hsh
        rcases hsh with ⟨hsh, _⟩ | rfl
        · exact Or.inl hsh
        · exact Or.inr (hChanges _ _ rfl rfl)
      · by_cases hThis : sh = Share.mk id_ to
        · subst hThis
          exact Or.inr (hChanges _ _ rfl rfl)
        · exact Or.inl (by simp [hsh, hThis])
      · simp only [List.mem_append, List.mem_filter, decide_eq_true_eq] at he
        rcases he with ⟨he, _⟩ | he
        · exact Or.inl he
        · cases u with
          | some u =>
            simp only [List.mem_singleton] at he
            subst he
            exact Or.inr (hChanges _ _ rfl rfl)
          | none => simp at he
      · by_cases hPair : e.record = id_ ∧ e.to = to
        · exact Or.inr (hChanges _ _ hPair.1 hPair.2)
        · exact Or.inl (List.mem_append_left _ (List.mem_filter.2 ⟨he, decide_eq_true hPair⟩))
    · simp only [applyWrite]
      rw [ite_eq_right hAllowed]
      exact kept s _ (fun h => h (fun hc => absurd hc hAllowed))
  | Unshare id_ to =>
    by_cases hAllowed : ownRecord s ⟨a, Change.Unshare id_ to⟩ id_
    · have hChanges : ∀ (i : Int) (c : TenantId), i = id_ → c = to →
          changesShare s ⟨a, Change.Unshare id_ to⟩ i c := by
        intro i c hi hc
        subst hi hc
        simp only [changesShare]
        exact ⟨⟨trivial, trivial⟩, hAllowed⟩
      simp only [applyWrite, takesEffect, onlyAsked, addsRecord]
      rw [ite_eq_left hAllowed]
      refine ⟨⟨⟨fun _ h => h, by simp⟩, fun _ => by simp⟩,
        ⟨⟨⟨⟨fun _ h => Or.inl h, fun sh hsh => Or.inl (List.mem_filter.1 hsh).1⟩, fun sh hsh => ?_⟩,
          fun e he => Or.inl (List.mem_filter.1 he).1⟩, fun e he => ?_⟩⟩
      · by_cases hThis : sh = Share.mk id_ to
        · subst hThis
          exact Or.inr (hChanges _ _ rfl rfl)
        · exact Or.inl (by simp [hsh, hThis])
      · by_cases hPair : e.record = id_ ∧ e.to = to
        · exact Or.inr (hChanges _ _ hPair.1 hPair.2)
        · exact Or.inl (List.mem_filter.2 ⟨he, decide_eq_true hPair⟩)
    · simp only [applyWrite]
      rw [ite_eq_right hAllowed]
      exact kept s _ (fun h => h (fun hc => absurd hc hAllowed))

end Crm.Lemmas

/-! The CRM's programs on the World: the screens' searches, the write side and the expiry job, each a run on the
database's field (and the clock's), the database's search a step of its field known only by what is assumed of it
(`within`). What each run leaves and gives, of a world meeting the database's rules: the screens change nothing and
answer from what the database's search returns; the write side holds the rows the write leads to and logs it; the
job stores again the rows of each record it changed and logs its run. -/

namespace Crm.Runs
open Crm Crm.Lemmas

/-- The database's search, run on the World: its run on the tables, the rest of the World as it was. -/
theorem fetch_run_eq (fetch : Account → Search → StateM Tables (List CrmRecord)) (u : Account) (q : Search)
    (w : World) : DatabaseModel.fetch_run fetch u q w =
      ((FrFlow.runOn (fetch u q) w.databaseModel).1,
        { w with databaseModel := (FrFlow.runOn (fetch u q) w.databaseModel).2 }) := rfl

/-- The records screen's run: what the search returns, of the user's company or shared with it at the clock's time,
by the store the database holds; the World as the search left it. -/
theorem search_run_eq (fetch : Account → Search → StateM Tables (List CrmRecord)) (u : Account) (q : Search)
    (w : World) : search_run fetch u q w =
      ((FrFlow.runOn (fetch u q) w.databaseModel).1.filter
          (fun r => decide (mayRead w.databaseModel.store w.clockModel u r)),
        { w with databaseModel := (FrFlow.runOn (fetch u q) w.databaseModel).2 }) := by
  simp only [search_run, search, FrFlow.runOn_bind, FrFlow.runOn_pure, ClockModel.Ops.now_onWorld,
    DatabaseModel.Ops.load_onWorld, DatabaseModel.Ops.onState_onWorld, FrFlow.runOn_within, ClockModel.now,
    DatabaseModel.load, FrFlow.runOn_get]
  congr

/-- The sales screen's run: the records screen's, deals only. -/
theorem dealsOf_run_eq (fetch : Account → Search → StateM Tables (List CrmRecord)) (u : Account) (q : Search)
    (w : World) : dealsOf_run fetch u q w =
      (((FrFlow.runOn (fetch u q) w.databaseModel).1.filter
          (fun r => decide (mayRead w.databaseModel.store w.clockModel u r))).filter (fun r => decide (r.kind = Kind.Deal)),
        { w with databaseModel := (FrFlow.runOn (fetch u q) w.databaseModel).2 }) := by
  simp only [dealsOf_run, dealsOf, FrFlow.runOn_bind, FrFlow.runOn_pure, ClockModel.Ops.now_onWorld,
    DatabaseModel.Ops.load_onWorld, DatabaseModel.Ops.onState_onWorld, FrFlow.runOn_within, ClockModel.now,
    DatabaseModel.load, FrFlow.runOn_get]
  congr

/-- What the database's search gives and leaves, of a world meeting the rules, by what is assumed of it: exactly the
stored records that match, the tables as they were. -/
theorem fetched (fetch : Account → Search → StateM Tables (List CrmRecord)) (hR : recordsByQuery.claim fetch)
    (hK : searchKeeps.claim fetch) (u : Account) (q : Search) (w : World) (hw : crmRun w.databaseModel ∧ keyedTables w.databaseModel.store ∧ oneRowPerKey w.databaseModel.store) :
    (FrFlow.runOn (fetch u q) w.databaseModel).2 = w.databaseModel ∧
      ∀ r, r ∈ (FrFlow.runOn (fetch u q) w.databaseModel).1 ↔ r ∈ w.databaseModel.store.records ∧ «matches» q r := by
  have hr := hR u q w hw.1 hw.2.1 hw.2.2
  have hk := hK u q w hw.1 hw.2.1 hw.2.2
  rw [fetch_run_eq] at hr hk
  simp only at hr hk
  exact ⟨hk, fun r => ⟨fun h => hr.1 r h, fun ⟨h1, h2⟩ => hr.2 r h1 h2⟩⟩

/-- The records screen, of a world meeting the rules: the World as it was; exactly the stored records that match and
the user may read. -/
theorem searched (fetch : Account → Search → StateM Tables (List CrmRecord)) (hR : recordsByQuery.claim fetch)
    (hK : searchKeeps.claim fetch) (u : Account) (q : Search) (w : World) (hw : crmRun w.databaseModel ∧ keyedTables w.databaseModel.store ∧ oneRowPerKey w.databaseModel.store) :
    (search_run fetch u q w).2 = w ∧ ∀ r, r ∈ (search_run fetch u q w).1 ↔
      (r ∈ w.databaseModel.store.records ∧ «matches» q r) ∧ mayRead w.databaseModel.store w.clockModel u r := by
  obtain ⟨hk, hr⟩ := fetched fetch hR hK u q w hw
  rw [search_run_eq, hk]
  refine ⟨rfl, fun r => ?_⟩
  simp only [List.mem_filter, decide_eq_true_eq, hr]

/-- The sales screen, of a world meeting the rules: the World as it was; exactly the stored deals that match and the
user may read. -/
theorem dealt (fetch : Account → Search → StateM Tables (List CrmRecord)) (hR : recordsByQuery.claim fetch)
    (hK : searchKeeps.claim fetch) (u : Account) (q : Search) (w : World) (hw : crmRun w.databaseModel ∧ keyedTables w.databaseModel.store ∧ oneRowPerKey w.databaseModel.store) :
    (dealsOf_run fetch u q w).2 = w ∧ ∀ r, r ∈ (dealsOf_run fetch u q w).1 ↔
      (((r ∈ w.databaseModel.store.records ∧ r.kind = Kind.Deal) ∧ «matches» q r) ∧
        mayRead w.databaseModel.store w.clockModel u r) := by
  obtain ⟨hk, hr⟩ := fetched fetch hR hK u q w hw
  rw [dealsOf_run_eq, hk]
  refine ⟨rfl, fun r => ?_⟩
  simp only [List.mem_filter, decide_eq_true_eq, hr]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨⟨h1, h4⟩, h2⟩, h3⟩
  · rintro ⟨⟨⟨h1, h4⟩, h2⟩, h3⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- The write side's run: the rows the write leads to about its record held, the write logged, those rows given. -/
theorem saved_run_eq (c : WriteCmd) (w : World) : saved_run c w =
    (aboutRecord (applyWrite w.databaseModel.store c) (about c),
      { w with databaseModel := Tables.mk (afterSave w.databaseModel.store c) (w.databaseModel.events ++ [Event.Wrote c]) }) := by
  simp only [saved_run, saved, FrFlow.runOn_bind, FrFlow.runOn_pure, DatabaseModel.Ops.load_onWorld,
    DatabaseModel.Ops.storeAbout_onWorld, DatabaseModel.Ops.logEvent_onWorld, FrFlow.runOn_within,
    DatabaseModel.load, DatabaseModel.storeAbout, DatabaseModel.logEvent, FrFlow.runOn_get, FrFlow.runOn_set,
    afterSave]

/-- A run of the expiry job: what `expire` makes of what the database holds, each changed record's rows stored
again, the run logged; that store given. -/
theorem expireOnce_run_eq (expire : CrmStore → Int → CrmStore) (now : Int) (w : World) :
    expireOnce_run expire now w = (expire w.databaseModel.store now,
      { w with databaseModel := Tables.mk ((idsIn w.databaseModel.store ++ idsIn (expire w.databaseModel.store now)).foldl (fun x i => if ¬aboutRecord w.databaseModel.store i = aboutRecord (expire w.databaseModel.store now) i then replaceAbout x i (aboutRecord (expire w.databaseModel.store now) i) else x) w.databaseModel.store) (w.databaseModel.events ++ [Event.Expired now]) }) := by
  rcases w with ⟨⟨s, es⟩, clk⟩
  simp only [expireOnce_run, expireOnce, FrFlow.runOn_bind, FrFlow.runOn_pure, DatabaseModel.Ops.load_onWorld,
    DatabaseModel.Ops.storeAbout_onWorld, DatabaseModel.Ops.logEvent_onWorld, FrFlow.runOn_within,
    DatabaseModel.load, DatabaseModel.storeAbout, DatabaseModel.logEvent, FrFlow.runOn_get, FrFlow.runOn_set]
  rw [loop _ _ (fun x i => if ¬aboutRecord s i = aboutRecord (expire s now) i then
      { x with databaseModel := Tables.mk (replaceAbout x.databaseModel.store i (aboutRecord (expire s now) i)) x.databaseModel.events } else x) (by
    intro i x
    by_cases hc : ¬aboutRecord s i = aboutRecord (expire s now) i
    · simp only [hc, not_false_eq_true, ↓reduceIte, FrFlow.runOn_bind, FrFlow.runOn_pure, FrFlow.runOn_within,
        FrFlow.runOn_get, FrFlow.runOn_set]
    · simp only [hc, ↓reduceIte, FrFlow.runOn_pure])]
  rw [fold_world _ (fun i => ¬aboutRecord s i = aboutRecord (expire s now) i)]

/-- A run meeting what sharesExpire says of it is the job's code: the records, the shares and the expiries not
ended. -/
theorem expire_code (expire : CrmStore → Int → CrmStore) (h : sharesExpire.claim expire) (s : CrmStore)
    (hk : onePerKey s) (now : Int) : expire s now = expireCode s now := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := h s hk hk now
  rcases hx : expire s now with ⟨rs, ss, es⟩
  rw [hx] at h1 h2 h3
  simp only at h1 h2 h3
  simp only [expireCode, h1, h2, h3]

/-- What the job stores is jobDone, its rule's step. -/
theorem jobStored_code (s : CrmStore) (now : Int) :
    ((idsIn s ++ idsIn (expireCode s now)).foldl (fun x i => if ¬aboutRecord s i = aboutRecord (expireCode s now) i then replaceAbout x i (aboutRecord (expireCode s now) i) else x) s) = jobDone s now := rfl

/-- Either screen, of a world meeting the rules: exactly the stored records the search on it asks for and the user
may read. -/
theorem screened (fetch : Account → Search → StateM Tables (List CrmRecord)) (hR : recordsByQuery.claim fetch)
    (hK : searchKeeps.claim fetch) (u : Account) (q : Ask) (w : World) (hw : crmRun w.databaseModel ∧ keyedTables w.databaseModel.store ∧ oneRowPerKey w.databaseModel.store) (r : CrmRecord) :
    r ∈ onScreen q (search_run fetch u q.search w).1 (dealsOf_run fetch u q.search w).1 ↔
      (r ∈ w.databaseModel.store.records ∧ askMatches q r) ∧ mayRead w.databaseModel.store w.clockModel u r := by
  rcases q with ⟨sc, se⟩
  cases sc with
  | Records =>
    simp only [onScreen, askMatches]
    exact (searched fetch hR hK u se w hw).2 r
  | Sales =>
    simp only [onScreen, askMatches]
    rw [(dealt fetch hR hK u se w hw).2 r]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- What the job stores holds the same rows about every record as the store it stores from. -/
theorem jobStored_sameRows (s t : CrmStore) : sameRows ((idsIn s ++ idsIn t).foldl (fun x i => if ¬aboutRecord s i = aboutRecord t i then replaceAbout x i (aboutRecord t i) else x) s) t := by
  simp only [sameRows]
  intro j _
  rw [about_stored]
  split
  · rfl
  · rename_i hj
    by_cases hin : j ∈ idsIn s ++ idsIn t
    · exact Classical.byContradiction fun hne => hj ⟨hin, hne⟩
    · simp only [List.mem_append, not_or] at hin
      rw [about_absent _ _ hin.1, about_absent _ _ hin.2]

/-- The store a history and one more event lead to: that event's step on the store the history led to. -/
theorem runOf_snoc (es : List Event) (e : Event) : runOf (es ++ [e]) = stepOf (runOf es) e := by
  simp only [runOf, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The write side keeps what the database holds the history's: one write on. -/
theorem saved_crmRun (c : WriteCmd) (w : World) (h : crmRun w.databaseModel) :
    crmRun (saved_run c w).2.databaseModel := by
  rw [saved_run_eq]
  simp only [crmRun] at h ⊢
  rw [runOf_snoc, ← h]
  rfl

/-- The job, run as sharesExpire says, keeps what the database holds the history's: one run on. -/
theorem expired_crmRun (expire : CrmStore → Int → CrmStore) (hX : sharesExpire.claim expire) (now : Int) (w : World)
    (hw : crmRun w.databaseModel ∧ keyedTables w.databaseModel.store ∧ oneRowPerKey w.databaseModel.store) : crmRun (expireOnce_run expire now w).2.databaseModel := by
  have h1 := hw.1
  rw [expireOnce_run_eq, expire_code expire hX _ hw.2.1 now, jobStored_code]
  simp only [crmRun] at h1 ⊢
  rw [runOf_snoc, ← h1]
  rfl

/-- What the write side leaves holds one row per key. -/
theorem saved_onePerKey (c : WriteCmd) (w : World) (h : onePerKey w.databaseModel.store) :
    onePerKey (saved_run c w).2.databaseModel.store := by
  rw [saved_run_eq]
  exact replace_onePerKey _ _ _ h (applyWrite_onePerKey _ c h)

/-- What the job leaves holds one row per key. -/
theorem expired_onePerKey (expire : CrmStore → Int → CrmStore) (hX : sharesExpire.claim expire) (now : Int)
    (w : World) (h : onePerKey w.databaseModel.store) : onePerKey (expireOnce_run expire now w).2.databaseModel.store := by
  rw [expireOnce_run_eq]
  have ht : onePerKey (expire w.databaseModel.store now) :=
    endsDueAt_onePerKey _ now _ (hX _ h h now) h
  exact stored_onePerKey _ _ _ _ h ht

/-- Stores holding the same rows about every record hold the same records, shares and expiries. -/
theorem sameRows_mem (a b : CrmStore) (h : sameRows a b) :
    (∀ r, r ∈ a.records ↔ r ∈ b.records) ∧ (∀ sh, sh ∈ a.shares ↔ sh ∈ b.shares) ∧
      (∀ e, e ∈ a.expiries ↔ e ∈ b.expiries) := by
  simp only [sameRows] at h
  have hab : ∀ i, (i ∈ idsIn a ∨ i ∈ idsIn b) → aboutRecord a i = aboutRecord b i :=
    fun i hi => h i (List.mem_append.2 hi)
  refine ⟨fun r => ?_, fun sh => ?_, fun e => ?_⟩
  · have hr : ∀ s : CrmStore, r ∈ s.records ↔ r ∈ (aboutRecord s r.id_).records := by simp [aboutRecord]
    have hi : ∀ s : CrmStore, r ∈ s.records → r.id_ ∈ idsIn s := fun s hs => by
      simp only [idsIn, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨r, hs, rfl⟩)
    exact ⟨fun hx => by rw [hr] at hx ⊢; rw [← hab _ (Or.inl (hi a ((hr a).2 hx)))]; exact hx,
      fun hx => by rw [hr] at hx ⊢; rw [hab _ (Or.inr (hi b ((hr b).2 hx)))]; exact hx⟩
  · have hr : ∀ s : CrmStore, sh ∈ s.shares ↔ sh ∈ (aboutRecord s sh.record).shares := by simp [aboutRecord]
    have hi : ∀ s : CrmStore, sh ∈ s.shares → sh.record ∈ idsIn s := fun s hs => by
      simp only [idsIn, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨sh, hs, rfl⟩)
    exact ⟨fun hx => by rw [hr] at hx ⊢; rw [← hab _ (Or.inl (hi a ((hr a).2 hx)))]; exact hx,
      fun hx => by rw [hr] at hx ⊢; rw [hab _ (Or.inr (hi b ((hr b).2 hx)))]; exact hx⟩
  · have hr : ∀ s : CrmStore, e ∈ s.expiries ↔ e ∈ (aboutRecord s e.record).expiries := by simp [aboutRecord]
    have hi : ∀ s : CrmStore, e ∈ s.expiries → e.record ∈ idsIn s := fun s hs => by
      simp only [idsIn, List.mem_append, List.mem_map]; exact Or.inr ⟨e, hs, rfl⟩
    exact ⟨fun hx => by rw [hr] at hx ⊢; rw [← hab _ (Or.inl (hi a ((hr a).2 hx)))]; exact hx,
      fun hx => by rw [hr] at hx ⊢; rw [hab _ (Or.inr (hi b ((hr b).2 hx)))]; exact hx⟩

/-- What the job leaves, as its rule's step reads it, holds the job's store's rows. -/
theorem jobDone_mem (s : CrmStore) (now : Int) :
    (∀ r, r ∈ (jobDone s now).records ↔ r ∈ s.records) ∧
      (∀ sh, sh ∈ (jobDone s now).shares ↔ sh ∈ (expireCode s now).shares) ∧
      (∀ e, e ∈ (jobDone s now).expiries ↔ e ∈ (expireCode s now).expiries) := by
  have h := sameRows_mem _ _ (jobStored_sameRows s (expireCode s now))
  rw [jobStored_code] at h
  exact ⟨fun r => (h.1 r).trans (by simp [expireCode]), h.2.1, h.2.2⟩

/-- The job's rule's step keeps one row per key. -/
theorem jobDone_onePerKey (s : CrmStore) (now : Int) (h : onePerKey s) : onePerKey (jobDone s now) := by
  rw [← jobStored_code]
  exact stored_onePerKey _ _ _ _ h (endsDueAt_onePerKey s now _ ⟨⟨rfl, rfl⟩, rfl⟩ h)

/-- Each step of the database's rule keeps one row per key. -/
theorem stepOf_onePerKey (s : CrmStore) (e : Event) (h : onePerKey s) : onePerKey (stepOf s e) := by
  cases e with
  | Wrote c => exact replace_onePerKey _ _ _ h (applyWrite_onePerKey _ c h)
  | Expired now => exact jobDone_onePerKey s now h

/-! Each record's rows after a write's code and a run of the job's code depend on that record's rows alone: so stores
holding the same rows about every record are led by each step to stores that do too. -/

theorem exists_about (s : CrmStore) (i : Int) (P : CrmRecord → Prop) :
    (∃ x ∈ s.records, x.id_ = i ∧ P x) ↔ (∃ x ∈ (aboutRecord s i).records, x.id_ = i ∧ P x) := by
  simp only [aboutRecord, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, hi, hp⟩; exact ⟨x, ⟨hx, hi⟩, hi, hp⟩
  · rintro ⟨x, ⟨hx, _⟩, hi, hp⟩; exact ⟨x, hx, hi, hp⟩

theorem filter_about {α : Type} (f : α → Int) (p : α → Prop) [DecidablePred p] (xs : List α) (i : Int) :
    (xs.filter (fun x => decide (p x))).filter (fun x => decide (f x = i)) =
      ((xs.filter (fun x => decide (f x = i))).filter (fun x => decide (p x))).filter (fun x => decide (f x = i)) := by
  simp only [List.filter_filter]
  apply List.filter_congr; intro x _
  cases decide (p x) <;> cases decide (f x = i) <;> rfl

theorem applyWrite_local (s : CrmStore) (c : WriteCmd) :
    aboutRecord (applyWrite s c) (about c) = aboutRecord (applyWrite (aboutRecord s (about c)) c) (about c) := by
  rcases c with ⟨a, ch⟩
  cases ch with
  | Add r =>
    have h : (∃ x ∈ s.records, x.id_ = r.id_) ↔ (∃ x ∈ (aboutRecord s r.id_).records, x.id_ = r.id_) := by
      have := exists_about s r.id_ (fun _ => True); simpa using this
    dsimp only [about, applyWrite]
    by_cases hc : r.tenant = a.tenant ∧ ¬∃ x ∈ s.records, x.id_ = r.id_
    · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, fun hx => hc.2 (h.2 hx)⟩]
      simp only [aboutRecord, List.filter_append, List.filter_filter, Bool.and_self]
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ⟨h'.1, fun hx => h'.2 (h.1 hx)⟩)]
      simp only [aboutRecord, List.filter_filter, Bool.and_self]
  | ShareWith i to u =>
    have h := exists_about s i (fun x => x.tenant = a.tenant)
    dsimp only [about, applyWrite]
    by_cases hc : ownRecord s ⟨a, Change.ShareWith i to u⟩ i
    · have hc2 : ownRecord (aboutRecord s i) ⟨a, Change.ShareWith i to u⟩ i := by simp only [ownRecord] at hc ⊢; exact h.1 hc
      rw [ite_eq_left hc, ite_eq_left hc2]
      simp only [aboutRecord, List.filter_append, CrmStore.mk.injEq, List.filter_filter, Bool.and_self]
      refine ⟨trivial, ?_, ?_⟩
      · congr 1; simp only [← List.filter_filter]; rw [filter_about (fun sh : Share => sh.record) (fun sh => ¬sh = Share.mk i to) s.shares i]
      · congr 1; simp only [← List.filter_filter]; rw [filter_about (fun e : Expiry => e.record) (fun e => ¬(e.record = i ∧ e.to = to)) s.expiries i]
    · have hc2 : ¬ownRecord (aboutRecord s i) ⟨a, Change.ShareWith i to u⟩ i := by
        simp only [ownRecord] at hc ⊢; exact fun h' => hc (h.2 h')
      rw [ite_eq_right hc, ite_eq_right hc2]
      simp only [aboutRecord, List.filter_filter, Bool.and_self]
  | Unshare i to =>
    have h := exists_about s i (fun x => x.tenant = a.tenant)
    dsimp only [about, applyWrite]
    by_cases hc : ownRecord s ⟨a, Change.Unshare i to⟩ i
    · have hc2 : ownRecord (aboutRecord s i) ⟨a, Change.Unshare i to⟩ i := by simp only [ownRecord] at hc ⊢; exact h.1 hc
      rw [ite_eq_left hc, ite_eq_left hc2]
      simp only [aboutRecord, CrmStore.mk.injEq, List.filter_filter, Bool.and_self]
      refine ⟨trivial, ?_, ?_⟩
      · simp only [← List.filter_filter]; rw [filter_about (fun sh : Share => sh.record) (fun sh => ¬sh = Share.mk i to) s.shares i]
      · simp only [← List.filter_filter]; rw [filter_about (fun e : Expiry => e.record) (fun e => ¬(e.record = i ∧ e.to = to)) s.expiries i]
    · have hc2 : ¬ownRecord (aboutRecord s i) ⟨a, Change.Unshare i to⟩ i := by
        simp only [ownRecord] at hc ⊢; exact fun h' => hc (h.2 h')
      rw [ite_eq_right hc, ite_eq_right hc2]
      simp only [aboutRecord, List.filter_filter, Bool.and_self]

theorem ended_local (sh : Share) (s : CrmStore) (now i : Int) (h : sh.record = i) :
    ended sh s now ↔ ended sh (aboutRecord s i) now := by
  simp only [ended, aboutRecord, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, hp, hle⟩; exact ⟨e, ⟨he, hp.1.trans h⟩, hp, hle⟩
  · rintro ⟨e, ⟨he, _⟩, hp, hle⟩; exact ⟨e, he, hp, hle⟩

theorem expire_local (s : CrmStore) (now i : Int) :
    aboutRecord (expireCode s now) i = aboutRecord (expireCode (aboutRecord s i) now) i := by
  simp only [expireCode, aboutRecord, CrmStore.mk.injEq, List.filter_filter]
  refine ⟨?_, ?_, ?_⟩
  · apply List.filter_congr; intro x _; cases decide (x.id_ = i) <;> rfl
  · apply List.filter_congr; intro x _
    by_cases hx : x.record = i
    · have := ended_local x s now i hx
      simp only [hx, decide_true, Bool.and_true, Bool.true_and]
      simp only [aboutRecord] at this
      rw [this]; congr
    · simp [hx]
  · apply List.filter_congr; intro x _
    by_cases hx : x.record = i
    · have := ended_local (Share.mk i x.to) s now i rfl
      simp only [hx, decide_true, Bool.and_true, Bool.true_and]
      simp only [aboutRecord] at this
      rw [this]
    · simp [hx]

theorem jobDone_about (s : CrmStore) (now j : Int) : aboutRecord (jobDone s now) j = aboutRecord (expireCode s now) j := by
  rw [← jobStored_code]
  rw [about_stored]
  split
  · rfl
  · rename_i hj
    by_cases hin : j ∈ idsIn s ++ idsIn (expireCode s now)
    · exact Classical.byContradiction fun hne => hj ⟨hin, hne⟩
    · simp only [List.mem_append, not_or] at hin
      rw [about_absent _ _ hin.1, about_absent _ _ hin.2]


/-- The records screen keeps readContract, of what is assumed of the database's search. -/
theorem read_contract (fetch : Account → Search → StateM Tables (List CrmRecord)) (hR : recordsByQuery.claim fetch)
    (hK : searchKeeps.claim fetch) : readContract.claim (search_run fetch) := by
  intro user query world h1 h2 h3
  have hr := (searched fetch hR hK user query world ⟨h1, h2, h3⟩).2
  revert hr
  generalize search_run fetch user query world = p
  rcases p with ⟨res, aft⟩
  intro hr
  exact ⟨fun r h => (hr r).1 h, fun r h1 h2 => (hr r).2 ⟨⟨h1, h2.1⟩, h2.2⟩⟩

/-- The sales screen keeps dealSearch, of what is assumed of the database's search. -/
theorem deal_search (fetch : Account → Search → StateM Tables (List CrmRecord)) (hR : recordsByQuery.claim fetch)
    (hK : searchKeeps.claim fetch) : dealSearch.claim (dealsOf_run fetch) := by
  intro user query world h1 h2 h3
  have hr := (dealt fetch hR hK user query world ⟨h1, h2, h3⟩).2
  revert hr
  generalize dealsOf_run fetch user query world = p
  rcases p with ⟨res, aft⟩
  intro hr
  exact ⟨fun r h => (hr r).1 h, fun r h1 h2 => (hr r).2 ⟨⟨⟨h1, h2.1.1⟩, h2.1.2⟩, h2.2⟩⟩

/-- A run of the job at `now`: a share holds at `T` after it exactly when it held both at `now` and at `T`. -/
theorem job_store (s t : CrmStore) (now T id_ : Int) (c : TenantId)
    (hShares : ∀ sh, sh ∈ t.shares ↔ sh ∈ s.shares ∧ ¬ended sh s now)
    (hExpiries : ∀ e, e ∈ t.expiries ↔ e ∈ s.expiries ∧ ¬ended (Share.mk e.record e.to) s now) :
    sharedNow t T id_ c ↔ sharedNow s now id_ c ∧ sharedNow s T id_ c := by
  simp only [sharedNow, hShares, hExpiries, ended]
  constructor
  · rintro ⟨⟨hIn, hNotNow⟩, hNoT⟩
    refine ⟨⟨hIn, hNotNow⟩, hIn, fun ⟨e, he, hPair, hLe⟩ => hNoT ⟨e, ⟨he, ?_⟩, hPair, hLe⟩⟩
    rw [hPair.1, hPair.2]
    exact hNotNow
  · rintro ⟨⟨hIn, hNotNow⟩, _, hNoT⟩
    exact ⟨⟨hIn, hNotNow⟩, fun ⟨e, ⟨he, _⟩, hPair, hLe⟩ => hNoT ⟨e, he, hPair, hLe⟩⟩

/-- Membership in a list filtered by a decided condition. -/
theorem mem_kept {α : Type} (xs : List α) (p : α → Prop) {d : DecidablePred p} (x : α) :
    x ∈ xs.filter (fun y => @decide (p y) (d y)) ↔ x ∈ xs ∧ p x :=
  ⟨fun h => ⟨(List.mem_filter.1 h).1, of_decide_eq_true (List.mem_filter.1 h).2⟩,
    fun ⟨h1, h2⟩ => List.mem_filter.2 ⟨h1, decide_eq_true h2⟩⟩

/-- A run of the job at `now`, in what users asked: one share per record and company, so a share holds at `T` after
it exactly when it held both at `now` and at `T`. -/
theorem job_asked (gs : List Grant) (now T id_ : Int) (c : TenantId)
    {d : ∀ g : Grant, Decidable (∀ t, g.«until» = some t → now < t)}
    (hUnique : ∀ g ∈ gs, ∀ g' ∈ gs, g.record = g'.record → g.to = g'.to → g = g') :
    (∃ g ∈ gs.filter (fun g => @decide (∀ t, g.«until» = some t → now < t) (d g)),
      (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.«until» = some t → T < t) ↔
    (∃ g ∈ gs, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.«until» = some t → now < t) ∧
    (∃ g ∈ gs, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.«until» = some t → T < t) := by
  constructor
  · rintro ⟨g, hg, hPair, hKeepT⟩
    obtain ⟨hIn, hKeepNow⟩ := List.mem_filter.1 hg
    exact ⟨⟨g, hIn, hPair, of_decide_eq_true hKeepNow⟩, ⟨g, hIn, hPair, hKeepT⟩⟩
  · rintro ⟨⟨g, hg, hPair, hKeepNow⟩, ⟨g', hg', hPair', hKeepT⟩⟩
    have hSame : g = g' := hUnique g hg g' hg' (hPair.1.trans hPair'.1.symm) (hPair.2.trans hPair'.2.symm)
    subst hSame
    exact ⟨g, List.mem_filter.2 ⟨hg, decide_eq_true hKeepNow⟩, hPair, hKeepT⟩

/-- A write that changes nothing it did not ask leaves every share it does not change as it held. -/
theorem frame_store (s t : CrmStore) (w : WriteCmd) (T id_ : Int) (c : TenantId)
    (hOnly : onlyAsked s w t) (hNot : ¬ changesShare s w id_ c) :
    sharedNow t T id_ c ↔ sharedNow s T id_ c := by
  obtain ⟨⟨⟨⟨_, hSharesT⟩, hSharesS⟩, hExpiriesT⟩, hExpiriesS⟩ := hOnly
  have hShare : Share.mk id_ c ∈ t.shares ↔ Share.mk id_ c ∈ s.shares :=
    ⟨fun h => (hSharesT _ h).resolve_right hNot, fun h => (hSharesS _ h).resolve_right hNot⟩
  have hExpiry : ∀ e : Expiry, e.record = id_ → e.to = c → (e ∈ t.expiries ↔ e ∈ s.expiries) := by
    intro e hRecord hTo
    have hNotE : ¬ changesShare s w e.record e.to := by rw [hRecord, hTo]; exact hNot
    exact ⟨fun h => (hExpiriesT e h).resolve_right hNotE, fun h => (hExpiriesS e h).resolve_right hNotE⟩
  simp only [sharedNow]
  constructor
  · rintro ⟨hIn, hNo⟩
    exact ⟨hShare.1 hIn, fun ⟨e, he, hPair, hLe⟩ => hNo ⟨e, (hExpiry e hPair.1 hPair.2).2 he, hPair, hLe⟩⟩
  · rintro ⟨hIn, hNo⟩
    exact ⟨hShare.2 hIn, fun ⟨e, he, hPair, hLe⟩ => hNo ⟨e, (hExpiry e hPair.1 hPair.2).1 he, hPair, hLe⟩⟩

/-- What users asked and what the CRM holds, from a store meeting the invariant, one event on. -/
theorem mirror_step (hTakesAll : writesTakeEffect.claim) (hOnlyAll : writesOnlyAsAsked.claim)
    (hKeptAll : recordsKept.claim) (s : CrmStore) (hk : onePerKey s) (A : Asked) (e : Event)
    (hRec : ∀ r, r ∈ s.records ↔ r ∈ A.records)
    (hShared : ∀ (id_ : Int) (c : TenantId) (T : Int), sharedNow s T id_ c ↔
      ∃ g ∈ A.grants, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.«until» = some t → T < t)
    (hUnique : ∀ g ∈ A.grants, ∀ g' ∈ A.grants, g.record = g'.record → g.to = g'.to → g = g') :
    (∀ r, r ∈ (stepOf s e).records ↔ r ∈ (askedStep A e).records) ∧
    ∀ (id_ : Int) (c : TenantId) (T : Int), sharedNow (stepOf s e) T id_ c ↔
      ∃ g ∈ (askedStep A e).grants, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.«until» = some t → T < t := by
  cases e with
  | Expired now =>
    obtain ⟨hRecords, hShares, hExpiries⟩ := jobDone_mem s now
    simp only [stepOf, askedStep]
    refine ⟨fun r => by rw [hRecords]; exact hRec r, fun id_ c T => ?_⟩
    rw [job_store s (jobDone s now) now T id_ c
      (fun sh => by rw [hShares]; simp only [expireCode]; exact mem_kept _ _ sh)
      (fun e => by rw [hExpiries]; simp only [expireCode]; exact mem_kept _ _ e), hShared id_ c now, hShared id_ c T]
    exact (job_asked A.grants now T id_ c hUnique).symm
  | Wrote w =>
    have hTakes := hTakesAll s hk hk w
    have hOnly := hOnlyAll s hk hk w
    have hKept := hKeptAll s hk hk (Event.Wrote w)
    simp only [stepOf] at hKept ⊢
    generalize afterSave s w = t at hTakes hOnly hKept ⊢
    have hOnlyRecords := hOnly.1.1.1.1
    rcases w with ⟨a, ch⟩
    cases ch with
    | Add r =>
      simp only [askedStep]
      have hFrame : ∀ id_ c T, sharedNow t T id_ c ↔ sharedNow s T id_ c :=
        fun id_ c T => frame_store s t _ T id_ c hOnly (by simp [changesShare])
      have hAllowedIff : (r.tenant = a.tenant ∧ ¬∃ x ∈ A.records, x.id_ = r.id_) ↔
          (r.tenant = a.tenant ∧ ¬∃ x ∈ s.records, x.id_ = r.id_) := by
        simp only [← hRec]
      by_cases hAllowed : r.tenant = a.tenant ∧ ¬∃ x ∈ s.records, x.id_ = r.id_
      · rw [ite_eq_left (hAllowedIff.2 hAllowed)]
        refine ⟨fun x => ?_, fun id_ c T => by rw [hFrame, hShared]⟩
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · intro hx
          rcases hOnlyRecords x hx with hs | hAdds
          · exact Or.inl ((hRec x).1 hs)
          · simp only [addsRecord] at hAdds
            exact Or.inr hAdds.1.1.symm
        · rintro (hx | rfl)
          · exact hKept x ((hRec x).2 hx)
          · simp only [takesEffect] at hTakes
            exact hTakes hAllowed
      · rw [ite_eq_right (fun h => hAllowed (hAllowedIff.1 h))]
        refine ⟨fun x => ⟨fun hx => ?_, fun hx => hKept x ((hRec x).2 hx)⟩, fun id_ c T => by rw [hFrame, hShared]⟩
        rcases hOnlyRecords x hx with hs | hAdds
        · exact (hRec x).1 hs
        · simp only [addsRecord] at hAdds
          obtain ⟨⟨hSame, hTenant⟩, hFresh⟩ := hAdds
          subst hSame
          exact absurd ⟨hTenant, hFresh⟩ hAllowed
    | ShareWith id0 to0 u =>
      have hRecT : ∀ x, x ∈ t.records ↔ x ∈ A.records := fun x =>
        ⟨fun hx => (hRec x).1 ((hOnlyRecords x hx).resolve_right (by simp [addsRecord])),
          fun hx => hKept x ((hRec x).2 hx)⟩
      simp only [askedStep]
      by_cases hAllowed : ∃ x ∈ s.records, x.id_ = id0 ∧ x.tenant = a.tenant
      · have hAllowedA : ∃ x ∈ A.records, x.id_ = id0 ∧ x.tenant = a.tenant := by
          simpa only [hRec] using hAllowed
        rw [ite_eq_left hAllowedA]
        refine ⟨hRecT, fun id_ c T => ?_⟩
        by_cases hPair : id_ = id0 ∧ c = to0
        · obtain ⟨rfl, rfl⟩ := hPair
          have hAsked : (∃ g ∈ A.grants.filter (fun g => decide (¬(g.record = id_ ∧ g.to = c))) ++
              [Grant.mk id_ c u], (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.«until» = some t → T < t) ↔
              ∀ t, u = some t → T < t := by
            constructor
            · rintro ⟨g, hg, hPairG, hKeep⟩
              rcases List.mem_append.1 hg with hg | hg
              · exact absurd hPairG (of_decide_eq_true (List.mem_filter.1 hg).2)
              · rw [List.mem_singleton] at hg
                subst hg
                exact hKeep
            · intro hKeep
              exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ⟨rfl, rfl⟩, hKeep⟩
          rw [hAsked]
          simp only [takesEffect, ownRecord] at hTakes
          obtain ⟨hIn, hTimes⟩ := hTakes hAllowed
          simp only [sharedNow]
          cases u with
          | some v =>
            obtain ⟨hHas, hOnlyV⟩ := hTimes
            constructor
            · rintro ⟨_, hNo⟩ t' hSome
              cases hSome
              exact Int.lt_of_not_ge (fun hLe => hNo ⟨_, hHas, ⟨rfl, rfl⟩, hLe⟩)
            · intro hKeep
              refine ⟨hIn, fun ⟨e, he, hPairE, hLe⟩ => ?_⟩
              have hUntil := hOnlyV e he hPairE
              have hLt := hKeep v rfl
              rw [hUntil] at hLe
              exact absurd hLe (Int.not_le.2 hLt)
          | none =>
            constructor
            · intro _ t' hNone
              cases hNone
            · intro _
              refine ⟨hIn, ?_⟩
              rintro ⟨e, he, hPairE, _⟩
              exact hTimes ⟨e, he, hPairE⟩
        · have hNot : ¬ changesShare s ⟨a, Change.ShareWith id0 to0 u⟩ id_ c := by
            simp only [changesShare]
            rintro ⟨⟨hRecord, hTo⟩, _⟩
            exact hPair ⟨hRecord.symm, hTo.symm⟩
          rw [frame_store s t _ T id_ c hOnly hNot, hShared, grant_append_other _ id0 to0 u T id_ c hPair,
            grant_filter_other A.grants id0 to0 T id_ c hPair]
      · have hNotA : ¬∃ x ∈ A.records, x.id_ = id0 ∧ x.tenant = a.tenant := by
          simpa only [hRec] using hAllowed
        rw [ite_eq_right hNotA]
        refine ⟨hRecT, fun id_ c T => ?_⟩
        have hNot : ¬ changesShare s ⟨a, Change.ShareWith id0 to0 u⟩ id_ c := by
          simp only [changesShare, ownRecord]
          rintro ⟨⟨hRecord, _⟩, hHeld⟩
          subst hRecord
          exact hAllowed hHeld
        rw [frame_store s t _ T id_ c hOnly hNot, hShared]
    | Unshare id0 to0 =>
      have hRecT : ∀ x, x ∈ t.records ↔ x ∈ A.records := fun x =>
        ⟨fun hx => (hRec x).1 ((hOnlyRecords x hx).resolve_right (by simp [addsRecord])),
          fun hx => hKept x ((hRec x).2 hx)⟩
      simp only [askedStep]
      by_cases hAllowed : ∃ x ∈ s.records, x.id_ = id0 ∧ x.tenant = a.tenant
      · have hAllowedA : ∃ x ∈ A.records, x.id_ = id0 ∧ x.tenant = a.tenant := by
          simpa only [hRec] using hAllowed
        rw [ite_eq_left hAllowedA]
        refine ⟨hRecT, fun id_ c T => ?_⟩
        by_cases hPair : id_ = id0 ∧ c = to0
        · obtain ⟨rfl, rfl⟩ := hPair
          simp only [takesEffect, ownRecord] at hTakes
          have hGone := hTakes hAllowed
          simp only [sharedNow]
          constructor
          · rintro ⟨hIn, _⟩
            exact absurd hIn hGone
          · rintro ⟨g, hg, hPairG, _⟩
            exact absurd hPairG (of_decide_eq_true (List.mem_filter.1 hg).2)
        · have hNot : ¬ changesShare s ⟨a, Change.Unshare id0 to0⟩ id_ c := by
            simp only [changesShare]
            rintro ⟨⟨hRecord, hTo⟩, _⟩
            exact hPair ⟨hRecord.symm, hTo.symm⟩
          rw [frame_store s t _ T id_ c hOnly hNot, hShared, grant_filter_other A.grants id0 to0 T id_ c hPair]
      · have hNotA : ¬∃ x ∈ A.records, x.id_ = id0 ∧ x.tenant = a.tenant := by
          simpa only [hRec] using hAllowed
        rw [ite_eq_right hNotA]
        refine ⟨hRecT, fun id_ c T => ?_⟩
        have hNot : ¬ changesShare s ⟨a, Change.Unshare id0 to0⟩ id_ c := by
          simp only [changesShare, ownRecord]
          rintro ⟨⟨hRecord, _⟩, hHeld⟩
          subst hRecord
          exact hAllowed hHeld
        rw [frame_store s t _ T id_ c hOnly hNot, hShared]

/-- What the CRM holds mirrors what users asked, by induction over its history, given what a write does and keeps. -/
theorem store_mirrors (h_writesTakeEffect : writesTakeEffect.claim) (h_writesOnlyAsAsked : writesOnlyAsAsked.claim)
    (h_recordsKept : recordsKept.claim) : storeMirrorsRequests.claim := by
  intro world h1 _ _
  have key := FrFlow.tracks (step := fun s e => stepOf s e) (init := CrmStore.mk [] [] [])
    (R := fun s es => onePerKey s ∧ (∀ r, r ∈ s.records ↔ r ∈ (askedIn es).records) ∧
      ∀ (id_ : Int) (c : TenantId) (T : Int), sharedNow s T id_ c ↔ sharedIn es id_ c T)
    (by
      refine ⟨by simp [onePerKey], fun r => ?_, fun id_ c T => ?_⟩
      · simp [askedIn]
      · simp [sharedNow, sharedIn, askedIn])
    (by
      intro s es e ⟨hs, hRec, hShared⟩
      refine ⟨stepOf_onePerKey s e hs, ?_⟩
      have hUnique := (askedIn_unique es).2
      simp only [sharedIn] at hShared ⊢
      rw [askedIn_snoc]
      generalize askedIn es = A at hRec hShared hUnique
      exact mirror_step h_writesTakeEffect h_writesOnlyAsAsked h_recordsKept s hs A e hRec hShared hUnique)
  obtain ⟨_, hRecords, hShared⟩ := key world.databaseModel.events
  simp only [crmRun, runOf] at h1
  rw [h1]
  exact ⟨fun r => propext (hRecords r), fun id_ c => propext (hShared id_ c world.clockModel)⟩

/-- A write's code does what was asked, and what the write side holds about the written record is what it leads to. -/
theorem writes_take_effect : writesTakeEffect.claim := by
  intro s hk ho w
  obtain ⟨⟨_, hTakes⟩, _⟩ := applyWrite_contract s hk ho w
  exact takesEffect_replace s (applyWrite s w) w hTakes

/-- A write's code changes nothing it was not asked, and the write side holds the store with its record's rows
replaced by those. -/
theorem writes_only_as_asked : writesOnlyAsAsked.claim := by
  intro s hk ho w
  obtain ⟨_, hOnly⟩ := applyWrite_contract s hk ho w
  exact onlyAsked_replace s (applyWrite s w) w hOnly

/-- No write and no run of the job removes a record. -/
theorem records_kept : recordsKept.claim := by
  intro s hk ho e r hr
  cases e with
  | Wrote w =>
    obtain ⟨⟨⟨hKeeps, _⟩, _⟩, _⟩ := applyWrite_contract s hk ho w
    simp only [stepOf, afterSave]
    rw [mem_records]
    by_cases hid : r.id_ = about w
    · exact Or.inr ⟨hKeeps r hr, hid⟩
    · exact Or.inl ⟨hr, hid⟩
  | Expired now =>
    simp only [stepOf]
    exact ((jobDone_mem s now).1 r).2 hr

/-- Either screen returns exactly the stored records the search asks for and the user may read now. -/
theorem visible (fetch : Account → Search → StateM Tables (List CrmRecord)) (hR : recordsByQuery.claim fetch)
    (hK : searchKeeps.claim fetch) : visibility.claim (search_run fetch) (dealsOf_run fetch) := by
  intro u q r world h1 h2 h3
  have hs := screened fetch hR hK u q world ⟨h1, h2, h3⟩ r
  revert hs
  generalize search_run fetch u q.search world = p1
  generalize dealsOf_run fetch u q.search world = p2
  rcases p1 with ⟨r1, a1⟩
  rcases p2 with ⟨r2, a2⟩
  intro hs
  exact propext hs

/-- The database answering with the stored records that match, its tables as they were, keeps what is assumed of its
search (today's `storedMatching`). -/
theorem matching_records : recordsByQuery.claim
    (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) := by
  intro u q w _ _ _
  rw [fetch_run_eq]
  simp only [FrFlow.runOn, StateT.run, Id.run, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun r h => h, fun r h1 h2 => ⟨h1, h2⟩⟩

theorem matching_keeps : searchKeeps.claim
    (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) :=
  fun _ _ _ _ _ _ => rfl

end Crm.Runs
