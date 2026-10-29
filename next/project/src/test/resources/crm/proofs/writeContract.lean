import FrFlowGen.Crm.writeContract.Spec

/-! `applyWrite` meets writeContract (today's proof): case by case on the change, and on whether its author's
company may make it. A write it may not make returns the store as it was. An add appends the one record asked; a
share or unshare of the author's record replaces only the share, and its time, of that record with the company
named, keeping every other row. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writeContract.Proofs
open Crm

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

theorem impl : Obl.impl := by
  unfold Obl.impl writeContract.claim
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

end Crm.writeContract.Proofs
