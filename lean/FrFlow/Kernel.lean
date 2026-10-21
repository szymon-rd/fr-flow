import FrFlow.Attr

/-!
# FrFlow kernel

A node of a FrFlow knowledge base is a `Machine`: states, events, the initial
states and the allowed steps. Its theorem is an invariant.

A child node is linked to its parent by a `Link`: an abstraction of its states
and of its events, such that every step of the child is a step of the parent,
or leaves the parent's state unchanged. `Link.transfer` carries every invariant
of the parent, and hence the root theorem, down to the child.

This file and `Auto.lean` are the trusted base. They are written by hand.
-/

namespace FrFlow

structure Machine where
  State : Type
  Event : Type
  init : State → Prop
  next : State → Event → State → Prop

/-- States reachable from an initial state. -/
inductive Reach (M : Machine) : M.State → Prop
  | init {s} : M.init s → Reach M s
  | step {s e t} : Reach M s → M.next s e t → Reach M t

/-- `P` holds in every reachable state of `M`. -/
def Invariant (M : Machine) (P : M.State → Prop) : Prop := ∀ s, Reach M s → P s

theorem Invariant.of_inductive {M : Machine} {P : M.State → Prop}
    (hinit : ∀ s, M.init s → P s) (hnext : ∀ s e t, P s → M.next s e t → P t) : Invariant M P := by
  intro s h
  induction h with
  | init hi => exact hinit _ hi
  | step _ hn ih => exact hnext _ _ _ ih hn

/-- A step of `M` for `some e`, or no change for `none`. -/
@[frflow_defs] def Step (M : Machine) (s : M.State) : Option M.Event → M.State → Prop
  | some e, t => M.next s e t
  | none, t => t = s

@[simp] theorem Step.some_iff {M : Machine} {s t : M.State} {e : M.Event} : Step M s (some e) t ↔ M.next s e t := Iff.rfl
@[simp] theorem Step.none_iff {M : Machine} {s t : M.State} : Step M s none t ↔ t = s := Iff.rfl

/-- `C` specializes `A`. `inv` is an invariant of `C` the step proof may rely on. -/
structure Link (C A : Machine) where
  abs : C.State → A.State
  event : C.State → C.Event → Option A.Event
  inv : C.State → Prop
  inv_holds : Invariant C inv
  init_ok : ∀ s, C.init s → A.init (abs s)
  next_ok : ∀ s e t, inv s → C.next s e t → Step A (abs s) (event s e) (abs t)

namespace Link
variable {C B A : Machine}

/-- Every reachable state of `C` maps to a reachable state of `A`. -/
theorem reach (L : Link C A) : ∀ {s}, Reach C s → Reach A (L.abs s) := by
  intro s h
  induction h with
  | init hi => exact .init (L.init_ok _ hi)
  | @step s e t hs hn ih =>
    have hstep := L.next_ok s e t (L.inv_holds s hs) hn
    cases he : L.event s e with
    | none => rw [he] at hstep; exact hstep ▸ ih
    | some a => rw [he] at hstep; exact .step ih hstep

/-- Invariants of the parent hold in the child. -/
theorem transfer (L : Link C A) {P : A.State → Prop} (h : Invariant A P) : Invariant C (fun s => P (L.abs s)) :=
  fun _ hs => h _ (L.reach hs)

end Link
end FrFlow
