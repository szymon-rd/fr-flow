/-!
# FrFlow kernel: transition systems and invariants

This file is part of the trusted kernel of FrFlow. It is written by hand,
never generated, and changes to it require review of every theory built on it.
-/

namespace FrFlow

/-- A state transition system. `Next` is the one-step relation. -/
structure Spec where
  State : Type
  Init  : State → Prop
  Next  : State → State → Prop

/-- States reachable from an initial state by finitely many steps. -/
inductive Reach (S : Spec) : S.State → Prop
  | init {s : S.State} : S.Init s → Reach S s
  | step {s s' : S.State} : Reach S s → S.Next s s' → Reach S s'

/-- `P` holds in every reachable state of `S`. -/
def Invariant (S : Spec) (P : S.State → Prop) : Prop :=
  ∀ s, Reach S s → P s

/-- An inductive predicate (established initially, preserved by every step)
is an invariant. -/
theorem Invariant.of_inductive {S : Spec} {P : S.State → Prop}
    (hinit : ∀ s, S.Init s → P s)
    (hstep : ∀ s s', P s → S.Next s s' → P s') :
    Invariant S P := by
  intro s h
  induction h with
  | init hi => exact hinit _ hi
  | step _ hn ih => exact hstep _ _ ih hn

theorem Invariant.mono {S : Spec} {P Q : S.State → Prop}
    (h : Invariant S P) (himp : ∀ s, P s → Q s) : Invariant S Q :=
  fun s hr => himp s (h s hr)

theorem Invariant.and {S : Spec} {P Q : S.State → Prop}
    (hP : Invariant S P) (hQ : Invariant S Q) : Invariant S (fun s => P s ∧ Q s) :=
  fun s hr => ⟨hP s hr, hQ s hr⟩

end FrFlow
