import FrFlow.Spec

/-!
# FrFlow kernel: refinement

A refinement of an abstract spec `A` by a concrete spec `C` is a forward
simulation with stuttering: an abstraction function `abs`, an inductive
gluing invariant `inv`, and the guarantee that every concrete step maps to
an abstract step or leaves the abstract state unchanged.

The central result is `Refinement.transfer`: every invariant (safety
property) of `A` holds, through `abs`, in every reachable state of `C`.
-/

namespace FrFlow

structure Refinement (C A : Spec) where
  abs     : C.State → A.State
  inv     : C.State → Prop
  init_ok : ∀ s, C.Init s → inv s ∧ A.Init (abs s)
  step_ok : ∀ s s', inv s → C.Next s s' →
              inv s' ∧ (A.Next (abs s) (abs s') ∨ abs s = abs s')

namespace Refinement

variable {C B A : Spec}

/-- Every reachable concrete state satisfies the gluing invariant and maps
to a reachable abstract state. -/
theorem reach (R : Refinement C A) :
    ∀ {s}, Reach C s → R.inv s ∧ Reach A (R.abs s) := by
  intro s h
  induction h with
  | init hi => exact ⟨(R.init_ok _ hi).1, .init (R.init_ok _ hi).2⟩
  | step _ hn ih =>
    obtain ⟨hinv, hra⟩ := ih
    obtain ⟨hinv', hor⟩ := R.step_ok _ _ hinv hn
    refine ⟨hinv', ?_⟩
    cases hor with
    | inl h => exact .step hra h
    | inr h => exact h ▸ hra

/-- The gluing invariant is an invariant of the concrete spec. -/
theorem invariant (R : Refinement C A) : Invariant C R.inv :=
  fun _ hr => (R.reach hr).1

/-- Safety transfer: abstract invariants hold in the concrete spec. -/
theorem transfer (R : Refinement C A) {P : A.State → Prop}
    (hP : Invariant A P) : Invariant C (fun c => P (R.abs c)) :=
  fun _ hr => hP _ (R.reach hr).2

/-- Refinement is transitive: a chain of proven links is a proven link. -/
def trans (R₁ : Refinement B A) (R₂ : Refinement C B) : Refinement C A where
  abs := fun c => R₁.abs (R₂.abs c)
  inv := fun c => R₂.inv c ∧ R₁.inv (R₂.abs c)
  init_ok := by
    intro s hs
    obtain ⟨h2, hb⟩ := R₂.init_ok s hs
    obtain ⟨h1, ha⟩ := R₁.init_ok _ hb
    exact ⟨⟨h2, h1⟩, ha⟩
  step_ok := by
    intro s s' ⟨h2, h1⟩ hn
    obtain ⟨h2', hor⟩ := R₂.step_ok s s' h2 hn
    cases hor with
    | inl hb =>
      obtain ⟨h1', hor'⟩ := R₁.step_ok _ _ h1 hb
      exact ⟨⟨h2', h1'⟩, hor'⟩
    | inr heq =>
      refine ⟨⟨h2', heq ▸ h1⟩, Or.inr ?_⟩
      rw [heq]

end Refinement
end FrFlow
