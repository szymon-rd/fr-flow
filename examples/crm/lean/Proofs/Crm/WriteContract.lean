import FrFlowGen.Crm.WriteContract.Spec

/-! Authored proof that `applyWrite` meets WriteContract: case by case on the change, and on whether
its author's company may make it. No case removes a record: an add appends one, the others keep them. A share or unshare of the author's record touches only the rows of
that record's id; with unique ids, no record of another company has that id. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.WriteContract.Proofs
open Crm.WriteContract

/-- A store with the same records and the same rows about an id holds them alike. -/
theorem rowsAlike_self (s : Crm.CrmStore) (rs : List Crm.CrmRecord) (id_ : Int) :
    Crm.rowsAlike s ⟨rs, s.shares, s.expiries⟩ id_ := by
  simp only [Crm.rowsAlike]
  exact ⟨⟨⟨fun _ h _ => h, fun _ h _ => h⟩, fun _ h _ => h⟩, fun _ h _ => h⟩

/-- With unique ids, a record of another company than `x`'s has another id than `x`. -/
theorem other_id (s : Crm.CrmStore) (hu : Crm.idsUnique s) (x r : Crm.CrmRecord) (hx : x ∈ s.records)
    (hr : r ∈ s.records) (ht : r.tenant ≠ x.tenant) : r.id_ ≠ x.id_ := by
  intro h
  simp only [Crm.idsUnique] at hu
  exact ht (congrArg Crm.CrmRecord.tenant (hu r hr x hx h))

theorem impl : Obl.impl := by
  unfold Obl.impl Crm.WriteContract.claim
  intro s w
  rcases w with ⟨a, ch⟩
  cases ch with
  | Add r =>
    simp only [Crm.WriteContract.post, Crm.applyWrite, Crm.takesEffect]
    by_cases hc : r.tenant = a.tenant ∧ ¬∃ x ∈ s.records, x.id_ = r.id_
    · rw [ite_eq_left hc]
      refine ⟨⟨⟨fun x hx => List.mem_append_left _ hx, ?_⟩, fun _ => by simp⟩, fun hu => ⟨?_, fun r' _ _ => rowsAlike_self s _ r'.id_⟩⟩
      · simp [List.filter_append, hc.1]
      · simp only [Crm.idsUnique] at hu ⊢
        intro x hx y hy hxy
        simp only [List.mem_append, List.mem_singleton] at hx hy
        rcases hx with hx | rfl <;> rcases hy with hy | rfl
        · exact hu x hx y hy hxy
        · exact absurd ⟨x, hx, hxy⟩ hc.2
        · exact absurd ⟨y, hy, hxy.symm⟩ hc.2
        · rfl
    · rw [ite_eq_right hc]
      exact ⟨⟨⟨fun _ h => h, rfl⟩, fun h => absurd h hc⟩, fun hu => ⟨hu, fun r' _ _ => rowsAlike_self s s.records r'.id_⟩⟩
  | ShareWith id_ to u =>
    simp only [Crm.WriteContract.post, Crm.applyWrite, Crm.takesEffect]
    by_cases hc : ∃ x ∈ s.records, x.id_ = id_ ∧ x.tenant = a.tenant
    · rw [ite_eq_left hc]
      obtain ⟨x, hx, hxi, hxa⟩ := hc
      refine ⟨⟨⟨fun _ h => h, rfl⟩, fun _ => ⟨by simp, ?_⟩⟩, fun hu => ⟨hu, fun r hr hra => ?_⟩⟩
      · cases u with
        | some u => simp
        | none =>
          simp only [List.append_nil, List.mem_filter, decide_eq_true_eq]
          rintro ⟨e, ⟨_, hne⟩, h1, h2⟩
          exact hne ⟨h1, h2⟩
      · have hne : r.id_ ≠ id_ := hxi ▸ other_id s hu x r hx hr (hxa ▸ hra)
        simp only [Crm.rowsAlike]
        refine ⟨⟨⟨fun sh hsh hshr => ?_, fun sh hsh hshr => ?_⟩, fun e he her => ?_⟩, fun e he her => ?_⟩
        · simp only [List.mem_append, List.mem_filter, List.mem_singleton, decide_eq_true_eq]
          exact Or.inl ⟨hsh, fun h => hne (hshr ▸ h ▸ rfl)⟩
        · simp only [List.mem_append, List.mem_filter, List.mem_singleton, decide_eq_true_eq] at hsh
          rcases hsh with ⟨hsh, _⟩ | rfl
          · exact hsh
          · exact absurd hshr.symm hne
        · simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
          exact Or.inl ⟨he, fun h => hne (her ▸ h.1)⟩
        · simp only [List.mem_append, List.mem_filter, decide_eq_true_eq] at he
          rcases he with ⟨he, _⟩ | he
          · exact he
          · cases u <;> simp at he
            subst he
            exact absurd her.symm hne
    · rw [ite_eq_right hc]
      exact ⟨⟨⟨fun _ h => h, rfl⟩, fun h => absurd h hc⟩, fun hu => ⟨hu, fun r' _ _ => rowsAlike_self s s.records r'.id_⟩⟩
  | Unshare id_ to =>
    simp only [Crm.WriteContract.post, Crm.applyWrite, Crm.takesEffect]
    by_cases hc : ∃ x ∈ s.records, x.id_ = id_ ∧ x.tenant = a.tenant
    · rw [ite_eq_left hc]
      obtain ⟨x, hx, hxi, hxa⟩ := hc
      refine ⟨⟨⟨fun _ h => h, rfl⟩, fun _ => by simp⟩, fun hu => ⟨hu, fun r hr hra => ?_⟩⟩
      have hne : r.id_ ≠ id_ := hxi ▸ other_id s hu x r hx hr (hxa ▸ hra)
      simp only [Crm.rowsAlike]
      refine ⟨⟨⟨fun sh hsh hshr => ?_, fun sh hsh hshr => ?_⟩, fun e he her => ?_⟩, fun e he her => ?_⟩
      · simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨hsh, fun h => hne (hshr ▸ h ▸ rfl)⟩
      · exact (List.mem_filter.1 hsh).1
      · simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨he, fun h => hne (her ▸ h.1)⟩
      · exact (List.mem_filter.1 he).1
    · rw [ite_eq_right hc]
      exact ⟨⟨⟨fun _ h => h, rfl⟩, fun h => absurd h hc⟩, fun hu => ⟨hu, fun r' _ _ => rowsAlike_self s s.records r'.id_⟩⟩

end Crm.WriteContract.Proofs
