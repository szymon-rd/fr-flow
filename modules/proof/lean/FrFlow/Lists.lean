/-!
List facts that `frflow_auto` (simp + grind) does not find by itself, for authored proofs.
-/

namespace FrFlow

/-- Filtering by `q` before a stronger `p` changes nothing: `p ⊆ q` makes the inner filter redundant. -/
theorem filter_filter_of_imp {α : Type} {p q : α → Bool} (l : List α)
    (h : ∀ x, p x = true → q x = true) : (l.filter q).filter p = l.filter p := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  cases hp : p x
  · simp
  · simp [h x hp]

/-- Filtering by a weaker `q` after `p` changes nothing: what passes `p` passes `q`. -/
theorem filter_filter_of_imp' {α : Type} {p q : α → Bool} (l : List α)
    (h : ∀ x, p x = true → q x = true) : (l.filter p).filter q = l.filter p := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  cases hp : p x
  · simp
  · simp [h x hp]

/-- Distinct keys identify entries: two entries of `l` with the same key `f` are the same entry
(use it when tokens, ids, … are distinct, i.e. `(l.map f).Nodup`). -/
theorem eq_of_nodup_map {α β : Type} {f : α → β} {l : List α} (hl : (l.map f).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (he : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hl
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd he.symm (hl.1 b hb)
    · exact absurd he (hl.1 a ha)
    · exact ih hl.2 ha hb

/-- Keys stay distinct when entries are removed by a filter. -/
theorem nodup_map_filter {α β : Type} {f : α → β} {l : List α} (p : α → Bool)
    (hl : (l.map f).Nodup) : ((l.filter p).map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hl
    cases hp : p x
    · simpa [List.filter_cons, hp] using ih hl.2
    · simp only [List.filter_cons, hp, ite_true, List.map_cons, List.nodup_cons, List.mem_map,
        List.mem_filter, not_exists, not_and]
      exact ⟨fun y hy he => hl.1 y hy.1 he, ih hl.2⟩

/-- Keys stay distinct when an entry with a fresh key is added at the end. -/
theorem nodup_map_snoc {α β : Type} {f : α → β} {l : List α} {x : α}
    (hl : (l.map f).Nodup) (hx : ∀ y ∈ l, f y ≠ f x) : ((l ++ [x]).map f).Nodup := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append, List.nodup_cons,
    List.not_mem_nil, List.nodup_nil, List.mem_map, List.mem_singleton]
  refine ⟨hl, ⟨not_false, trivial⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ _ rfl
  exact hx y hy

end FrFlow
