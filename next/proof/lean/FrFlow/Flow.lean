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
/-- A branch (`c.foldF(a, b)`, `whenA`, `unlessA`, `ifM`): the run of the branch taken. -/
@[frflow_defs ↓] theorem runOn_ite {σ α : Type} {c : Prop} {h : Decidable c} (x y : StateM σ α) (s : σ) :
    runOn (@ite _ c h x y) s = @ite _ c h (runOn x s) (runOn y s) := by
  split <;> rfl
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

/-- `xs.mapM f` (`traverse`): each element in turn, the results in order. -/
@[frflow_defs] theorem runOn_mapM_nil {σ α β : Type} (f : α → StateM σ β) (s : σ) :
    runOn (([] : List α).mapM f) s = ([], s) := rfl
@[frflow_defs] theorem runOn_mapM_cons {σ α β : Type} (f : α → StateM σ β) (x : α) (xs : List α) (s : σ) :
    runOn ((x :: xs).mapM f) s =
      ((runOn (f x) s).1 :: (runOn (xs.mapM f) (runOn (f x) s).2).1, (runOn (xs.mapM f) (runOn (f x) s).2).2) := by
  rw [List.mapM_cons]; rfl

/-- `xs.foldlM (init := b) f` (`foldM`): the accumulator through each element in turn. -/
@[frflow_defs] theorem runOn_foldlM_nil {σ α β : Type} (f : β → α → StateM σ β) (b : β) (s : σ) :
    runOn (([] : List α).foldlM f b) s = (b, s) := rfl
@[frflow_defs] theorem runOn_foldlM_cons {σ α β : Type} (f : β → α → StateM σ β) (b : β) (x : α) (xs : List α) (s : σ) :
    runOn ((x :: xs).foldlM f b) s = runOn (xs.foldlM f (runOn (f b x) s).1) (runOn (f b x) s).2 := by
  rw [List.foldlM_cons]; rfl

/-!
Flows that may fail. A flow whose boundary may fail, or that raises or handles errors, runs in
`ExceptT ε (StateM World)`: a step that fails changes nothing, the steps before it stay done, and
the run gives its outcome (`Except ε α`) and the world after (`runOnE`). A failing boundary's call
takes the next of the world's faults: `true` fails it (`failing`). The lemmas compute a run as
above; where the outcome depends on the faults, `split` takes each case.
-/

/-- A flow that may fail, run on the models from a world: its outcome and the world after. -/
def runOnE {σ ε α : Type} (x : ExceptT ε (StateM σ) α) (s : σ) : Except ε α × σ := runOn x.run s

/-- What a contract says of a run's outcome: `ok` of a result and the world after, `err` of an error and the world after. -/
@[frflow_defs] def outcome {σ ε α : Type} (ok : α → σ → Prop) (err : ε → σ → Prop) : Except ε α × σ → Prop
  | (.ok a, s) => ok a s
  | (.error e, s) => err e s

/-- A failing boundary's step: it takes the next of the faults (`faults`, put back with `rest`); on `true` it fails
with `e`, changing nothing else, otherwise (and when no fault is left) it is `x`. -/
def failing {σ ε α : Type} (faults : σ → List Bool) (rest : σ → List Bool → σ) (e : ε) (x : StateM σ α) :
    ExceptT ε (StateM σ) α :=
  ExceptT.mk fun s => match faults s with
    | true :: fs => (Except.error e, rest s fs)
    | false :: fs => (Except.ok (runOn x (rest s fs)).1, (runOn x (rest s fs)).2)
    | [] => (Except.ok (runOn x s).1, (runOn x s).2)

@[frflow_defs] theorem runOnE_pure {σ ε α : Type} (a : α) (s : σ) :
    runOnE (pure a : ExceptT ε (StateM σ) α) s = (.ok a, s) := rfl
@[frflow_defs] theorem runOnE_bind {σ ε α β : Type} (x : ExceptT ε (StateM σ) α) (f : α → ExceptT ε (StateM σ) β) (s : σ) :
    runOnE (x >>= f) s = match runOnE x s with
      | (.ok a, s') => runOnE (f a) s'
      | (.error e, s') => (.error e, s') := by
  show runOn (ExceptT.bind x f).run s = _
  simp only [runOnE, runOn, ExceptT.run, ExceptT.bind, ExceptT.mk]
  show (StateT.run (StateT.bind x _) s).run = _
  simp only [StateT.run, StateT.bind, bind]
  generalize x s = p
  rcases p with ⟨r, s'⟩
  cases r <;> rfl
@[frflow_defs] theorem runOnE_map {σ ε α β : Type} (f : α → β) (x : ExceptT ε (StateM σ) α) (s : σ) :
    runOnE (f <$> x) s = match runOnE x s with
      | (.ok a, s') => (.ok (f a), s')
      | (.error e, s') => (.error e, s') := by
  rw [← bind_pure_comp, runOnE_bind]
  generalize runOnE x s = p
  rcases p with ⟨r, s'⟩
  cases r <;> rfl
@[frflow_defs] theorem runOnE_seqRight {σ ε α β : Type} (x : ExceptT ε (StateM σ) α) (y : ExceptT ε (StateM σ) β) (s : σ) :
    runOnE (x *> y) s = match runOnE x s with
      | (.ok _, s') => runOnE y s'
      | (.error e, s') => (.error e, s') := by
  rw [seqRight_eq_bind, runOnE_bind]
@[frflow_defs] theorem runOnE_throw {σ ε α : Type} (e : ε) (s : σ) :
    runOnE (throwThe ε e : ExceptT ε (StateM σ) α) s = (.error e, s) := rfl
@[frflow_defs] theorem runOnE_tryCatch {σ ε α : Type} (x : ExceptT ε (StateM σ) α) (h : ε → ExceptT ε (StateM σ) α) (s : σ) :
    runOnE (tryCatchThe ε x h) s = match runOnE x s with
      | (.ok a, s') => (.ok a, s')
      | (.error e, s') => runOnE (h e) s' := by
  show runOn (ExceptT.tryCatch x h).run s = _
  simp only [runOnE, runOn, ExceptT.tryCatch, ExceptT.run, ExceptT.mk]
  show (StateT.run (StateT.bind x _) s).run = _
  simp only [StateT.run, StateT.bind, bind]
  generalize x s = p
  rcases p with ⟨r, s'⟩
  cases r <;> rfl
/-- A step of a boundary that never fails, in a flow that may. -/
@[frflow_defs] theorem runOnE_lift {σ ε α : Type} (x : StateM σ α) (s : σ) :
    runOnE (ExceptT.lift x : ExceptT ε (StateM σ) α) s = (.ok (runOn x s).1, (runOn x s).2) := rfl
@[frflow_defs] theorem runOnE_failing {σ ε α : Type} (faults : σ → List Bool) (rest : σ → List Bool → σ) (e : ε)
    (x : StateM σ α) (s : σ) :
    runOnE (failing faults rest e x) s = match faults s with
      | true :: fs => (.error e, rest s fs)
      | false :: fs => (.ok (runOn x (rest s fs)).1, (runOn x (rest s fs)).2)
      | [] => (.ok (runOn x s).1, (runOn x s).2) := by
  simp only [runOnE, failing, ExceptT.run, ExceptT.mk]
  unfold runOn
  simp only [StateT.run]
  rcases h : faults s with _ | ⟨b, fs⟩
  · rfl
  · cases b <;> rfl
@[frflow_defs ↓] theorem runOnE_ite {σ ε α : Type} {c : Prop} {h : Decidable c} (x y : ExceptT ε (StateM σ) α) (s : σ) :
    runOnE (@ite _ c h x y) s = @ite _ c h (runOnE x s) (runOnE y s) := by
  split <;> rfl
@[frflow_defs] theorem runOnE_forIn_nil {σ ε β α : Type} (b : β) (f : α → β → ExceptT ε (StateM σ) (ForInStep β)) (s : σ) :
    runOnE (forIn ([] : List α) b f) s = (.ok b, s) := rfl
@[frflow_defs] theorem runOnE_forIn_cons {σ ε β α : Type} (x : α) (xs : List α) (b : β)
    (f : α → β → ExceptT ε (StateM σ) (ForInStep β)) (s : σ) :
    runOnE (forIn (x :: xs) b f) s =
      match runOnE (f x b) s with
      | (.ok (ForInStep.done b'), s') => (.ok b', s')
      | (.ok (ForInStep.yield b'), s') => runOnE (forIn xs b' f) s'
      | (.error e, s') => (.error e, s') := by
  rw [List.forIn_cons, runOnE_bind]
  generalize runOnE (f x b) s = p
  rcases p with ⟨r, s'⟩
  rcases r with e | r
  · rfl
  · cases r <;> rfl
@[frflow_defs] theorem runOnE_mapM_nil {σ ε α β : Type} (f : α → ExceptT ε (StateM σ) β) (s : σ) :
    runOnE (([] : List α).mapM f) s = (.ok [], s) := rfl
@[frflow_defs] theorem runOnE_foldlM_nil {σ ε α β : Type} (f : β → α → ExceptT ε (StateM σ) β) (b : β) (s : σ) :
    runOnE (([] : List α).foldlM f b) s = (.ok b, s) := rfl
@[frflow_defs] theorem runOnE_foldlM_cons {σ ε α β : Type} (f : β → α → ExceptT ε (StateM σ) β) (b : β) (x : α) (xs : List α)
    (s : σ) :
    runOnE ((x :: xs).foldlM f b) s = match runOnE (f b x) s with
      | (.ok b', s') => runOnE (xs.foldlM f b') s'
      | (.error e, s') => (.error e, s') := by
  rw [List.foldlM_cons, runOnE_bind]

end FrFlow
