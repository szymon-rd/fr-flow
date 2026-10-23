import FrFlow.Attr

/-!
Flows on the boundaries' models. A flow is a `do` block over any monad with the boundaries'
operations; the proofs run it in `StateM World`, where `World` holds each model's state and each
boundary's operations are its model's, on that model's part of the world (`within`).
`frflow_defs` computes a run step by step: `simp only [frflow_defs]` turns `runOn f w` into what
the steps do to `w`.
-/

namespace FrFlow

/-- A flow run on the models from a world: its result and the world after. -/
def runOn {σ α : Type} (x : StateM σ α) (s : σ) : α × σ := (x.run s).run

/-- A step over one part of a state, run on the whole: the part read, changed, put back. -/
def within {σ τ α : Type} (get : σ → τ) (put : σ → τ → σ) (x : StateM τ α) : StateM σ α :=
  fun s => pure ((runOn x (get s)).1, put s (runOn x (get s)).2)

@[frflow_defs] theorem runOn_pure {σ α : Type} (a : α) (s : σ) : runOn (pure a : StateM σ α) s = (a, s) := rfl
@[frflow_defs] theorem runOn_bind {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    runOn (x >>= f) s = runOn (f (runOn x s).1) (runOn x s).2 := rfl
@[frflow_defs] theorem runOn_map {σ α β : Type} (f : α → β) (x : StateM σ α) (s : σ) :
    runOn (f <$> x) s = (f (runOn x s).1, (runOn x s).2) := rfl
@[frflow_defs] theorem runOn_seqRight {σ α β : Type} (x : StateM σ α) (y : StateM σ β) (s : σ) :
    runOn (x *> y) s = runOn y (runOn x s).2 := rfl
@[frflow_defs] theorem runOn_get {σ : Type} (s : σ) : runOn (get : StateM σ σ) s = (s, s) := rfl
@[frflow_defs] theorem runOn_set {σ : Type} (t s : σ) : runOn (set t : StateM σ PUnit) s = (⟨⟩, t) := rfl
@[frflow_defs] theorem runOn_modify {σ : Type} (f : σ → σ) (s : σ) : runOn (modify f : StateM σ PUnit) s = (⟨⟩, f s) := rfl
@[frflow_defs] theorem runOn_within {σ τ α : Type} (get : σ → τ) (put : σ → τ → σ) (x : StateM τ α) (s : σ) :
    runOn (within get put x) s = ((runOn x (get s)).1, put s (runOn x (get s)).2) := rfl
@[frflow_defs] theorem runOn_forIn_nil {σ β α : Type} (b : β) (f : α → β → StateM σ (ForInStep β)) (s : σ) :
    runOn (forIn ([] : List α) b f) s = (b, s) := rfl
@[frflow_defs] theorem runOn_forIn_cons {σ β α : Type} (x : α) (xs : List α) (b : β) (f : α → β → StateM σ (ForInStep β)) (s : σ) :
    runOn (forIn (x :: xs) b f) s =
      match runOn (f x b) s with
      | (ForInStep.done b', s') => (b', s')
      | (ForInStep.yield b', s') => runOn (forIn xs b' f) s' := by
  rw [List.forIn_cons, runOn_bind]
  generalize runOn (f x b) s = p
  rcases p with ⟨r, s'⟩
  cases r <;> rfl

/-- A loop whose body yields nothing (`for x in xs do g x`): the state goes through each step in turn. -/
@[frflow_defs] theorem runOn_forIn_unit {σ α : Type} (xs : List α) (g : α → StateM σ PUnit) (s : σ) :
    runOn (forIn xs PUnit.unit (fun x (_ : PUnit) => do g x; pure (ForInStep.yield PUnit.unit))) s =
      (PUnit.unit, xs.foldl (fun s x => (runOn (g x) s).2) s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [runOn_forIn_cons]; exact ih _

end FrFlow
