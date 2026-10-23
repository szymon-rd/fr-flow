import FrFlowGen.Crm.ExpiryJob.Spec

/-! The expiry job's flow, run on the database's model. The loop stores, for each record in
`changedIds`, the rows the new store has about it (`fold_world`); storing a record's rows changes what
the database holds about that record only (`about_replace`), so after the loop it holds the new
store's rows about every record the loop stored and its old rows about the others (`about_stored`).
A record not stored has the same rows in both stores: either `changedIds` left it out because they are
equal, or neither store mentions it (`about_absent`). So the database holds the same rows as the new
store about every record (`sameRows`); the run is logged last, and the flow returns the new store. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.ExpiryJob.Proofs
open Crm Crm.ExpiryJob

/-- One field of a store after a record's rows are stored, as `aboutRecord` reads it. -/
theorem filter_replace {α : Type} (f : α → Int) (xs ys : List α) (i j : Int) :
    List.filter (fun x => decide (f x = j)) (List.filter (fun x => decide (f x ≠ i)) xs ++ List.filter (fun x => decide (f x = i)) ys) =
      if j = i then List.filter (fun x => decide (f x = j)) ys else List.filter (fun x => decide (f x = j)) xs := by
  rw [List.filter_append, List.filter_filter, List.filter_filter]
  split
  · rename_i h
    subst h
    rw [List.filter_eq_nil_iff.mpr (fun x _ => by simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; exact fun h1 h2 => h2 h1), List.nil_append]
    apply List.filter_congr; intro x _; by_cases hx : f x = j <;> simp [hx]
  · rename_i h
    have hy : List.filter (fun a => decide (f a = j) && decide (f a = i)) ys = [] :=
      List.filter_eq_nil_iff.mpr (fun x _ => by simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; exact fun h1 h2 => h (h1 ▸ h2))
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

/-- After storing the new store's rows about each record of `ids`. -/
theorem about_stored (ids : List Int) (s t : CrmStore) (j : Int) :
    aboutRecord (ids.foldl (fun st i => replaceAbout st i (aboutRecord t i)) s) j =
      if j ∈ ids then aboutRecord t j else aboutRecord s j := by
  induction ids generalizing s with
  | nil => simp
  | cons i ids ih =>
    rw [List.foldl_cons, ih, about_replace]
    by_cases h1 : j ∈ ids <;> by_cases h2 : j = i <;> simp_all

/-- A store says nothing about a record it does not mention. -/
theorem about_absent (s : CrmStore) (j : Int) (h : j ∉ idsIn s) : aboutRecord s j = ⟨[], [], []⟩ := by
  simp only [idsIn, List.mem_append, List.mem_map, not_or, not_exists, not_and] at h
  obtain ⟨⟨hr, hs⟩, he⟩ := h
  simp only [aboutRecord, CrmStore.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> rw [List.filter_eq_nil_iff] <;> intro x hx <;> simp only [decide_eq_true_eq]
  · exact fun e => hr x hx e
  · exact fun e => hs x hx e
  · exact fun e => he x hx e

/-- The loop of the flow, on the models: the database's store goes through each record's rows stored in turn. -/
theorem fold_world (ids : List Int) (t : CrmStore) (w : World) :
    (ids.foldl (fun (s : World) i => { database := { store := replaceAbout s.database.store i (aboutRecord t i), events := s.database.events } }) w) =
      { database := { store := ids.foldl (fun st i => replaceAbout st i (aboutRecord t i)) w.database.store, events := w.database.events } } := by
  induction ids generalizing w with
  | nil => rfl
  | cons i ids ih => rw [List.foldl_cons, ih]; rfl

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro expire _
  simp only [Crm.ExpiryJob.claim]
  intro now w
  -- The run, step by step on the model; the domain's definitions stay folded.
  simp only [Crm.ExpiryJob.post, expireOnce_run, expireOnce, FrFlow.runOn_bind, FrFlow.runOn_pure,
    Database.load_onWorld, Database.storeAbout_onWorld, Database.logEvent_onWorld, FrFlow.runOn_within,
    DatabaseModel.load, DatabaseModel.storeAbout, DatabaseModel.logEvent, FrFlow.runOn_get, FrFlow.runOn_modify,
    FrFlow.runOn_forIn_unit]
  rw [fold_world]
  refine ⟨⟨?_, rfl⟩, trivial⟩
  -- The database then holds the new store's rows about every record.
  simp only [sameRows]
  intro j _
  rw [about_stored]
  split
  · rfl
  · rename_i hj
    simp only [changedIds, List.mem_filter, decide_eq_true_eq, not_and, not_not] at hj
    by_cases hin : j ∈ idsIn w.database.store ++ idsIn (expire w.database.store now)
    · exact hj hin
    · simp only [List.mem_append, not_or] at hin
      rw [about_absent _ _ hin.1, about_absent _ _ hin.2]

end Crm.ExpiryJob.Proofs
