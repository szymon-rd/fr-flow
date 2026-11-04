import FrFlow.Flow

/-!
Races. A program that races two branches gives the winner's result: the scheduler's choice of the
winner, which Lean leaves open. The loser runs until the winner finishes and is then cancelled,
between two of its steps (an operation's call, or a transaction, each all or nothing): what its
steps did until then is kept. So a race is read as the choice of the winner, then the loser's
steps until the scheduler cancels it (`cut`: before each of its steps, the choice of whether it is
cancelled there, `step`), then the winner's. A run takes each choice from the world's `races`, the
next of them in turn (`true`: the left wins; the loser is cancelled), `true` when none is left,
as the Scala tests' sequential runs do; a statement holds of every world, so of every choice.
-/

namespace FrFlow

/-- The scheduler's choice of a race's winner (`true`: the left). -/
class Races (m : Type → Type) where
  leftWins : m Bool

/-- The next of the choices a state holds (`races`, put back with `rest`): the left on `true`, and when none is
left. -/
def nextRace {σ : Type} (races : σ → List Bool) (rest : σ → List Bool → σ) : StateM σ Bool :=
  fun s => match races s with
    | b :: bs => (b, rest s bs)
    | [] => (true, s)

@[frflow_defs] theorem runOn_nextRace {σ : Type} (races : σ → List Bool) (rest : σ → List Bool → σ) (s : σ) :
    runOn (nextRace races rest) s = match races s with
      | b :: bs => (b, rest s bs)
      | [] => (true, s) := rfl

/-- A step of a race's loser: the scheduler's choice of whether the loser is cancelled before it (`true`: it is, and
gives nothing), then the step. -/
def Races.step {m : Type → Type} {α : Type} [Monad m] [Races m] (x : m α) : OptionT m α :=
  OptionT.mk do if (← Races.leftWins) then pure none else some <$> x

/-- A race's loser until it is cancelled: what its steps did kept, its result dropped. -/
def Races.cut {m : Type → Type} {α : Type} [Monad m] (x : OptionT m α) : m Unit := do
  let _ ← x.run
  pure ()

/-- A traverse at once in a race's loser: each branch runs until it is cancelled at its own step (the branches read in
turn); the results when none was, and nothing, the rest of the loser dropped, when one was. -/
def Races.each {m : Type → Type} {α β : Type} [Monad m] (xs : List α) (f : α → OptionT m β) : OptionT m (List β) :=
  OptionT.mk do
    let os ← xs.mapM (fun x => (f x).run)
    pure (os.mapM id)

/-- In a program that may fail, the choice is made as in one that may not. -/
instance {ε : Type} {m : Type → Type} [Monad m] [Races m] : Races (ExceptT ε m) := ⟨ExceptT.lift Races.leftWins⟩

@[frflow_defs] theorem Races.leftWins_exceptT {ε : Type} {m : Type → Type} [Monad m] [Races m] :
    (Races.leftWins : ExceptT ε m Bool) = ExceptT.lift Races.leftWins := rfl

/-! A loser's run, step by step: `frflow_defs` turns the run of `cut x` into the runs of `x`'s steps, each a choice
then the step, the rest of `x` dropped once a step gives nothing. -/

@[frflow_defs] theorem runOn_cut {σ α : Type} (x : OptionT (StateM σ) α) (s : σ) :
    runOn (Races.cut x) s = ((), (runOn x.run s).2) := rfl
@[frflow_defs] theorem runOn_optionT_pure {σ α : Type} (a : α) (s : σ) :
    runOn (pure a : OptionT (StateM σ) α).run s = (some a, s) := rfl
@[frflow_defs] theorem runOn_optionT_bind {σ α β : Type} (x : OptionT (StateM σ) α) (f : α → OptionT (StateM σ) β)
    (s : σ) : runOn (x >>= f).run s = match runOn x.run s with
      | (some a, s') => runOn (f a).run s'
      | (none, s') => (none, s') := by
  show runOn (x.run >>= fun o => match o with | some a => (f a).run | none => pure none) s = _
  rw [runOn_bind]
  generalize runOn x.run s = p
  rcases p with ⟨o, s'⟩
  cases o <;> rfl
@[frflow_defs] theorem runOn_step {σ α : Type} [Races (StateM σ)] (x : StateM σ α) (s : σ) :
    runOn (Races.step x).run s = match runOn (Races.leftWins : StateM σ Bool) s with
      | (true, s') => (none, s')
      | (false, s') => (some (runOn x s').1, (runOn x s').2) := by
  show runOn (Races.leftWins >>= fun b => if b then pure none else some <$> x) s = _
  rw [runOn_bind]
  generalize runOn (Races.leftWins : StateM σ Bool) s = p
  rcases p with ⟨b, s'⟩
  cases b <;> rfl
@[frflow_defs ↓] theorem runOn_optionT_ite {σ α : Type} {c : Prop} {h : Decidable c} (x y : OptionT (StateM σ) α)
    (s : σ) : runOn (@ite _ c h x y).run s = @ite _ c h (runOn x.run s) (runOn y.run s) := by
  split <;> rfl
@[frflow_defs] theorem runOn_optionT_mapM_nil {σ α β : Type} (f : α → OptionT (StateM σ) β) (s : σ) :
    runOn (([] : List α).mapM f).run s = (some [], s) := rfl
@[frflow_defs] theorem runOn_optionT_mapM_cons {σ α β : Type} (f : α → OptionT (StateM σ) β) (x : α) (xs : List α)
    (s : σ) : runOn ((x :: xs).mapM f).run s = match runOn (f x).run s with
      | (some b, s') => match runOn (xs.mapM f).run s' with
        | (some bs, s'') => (some (b :: bs), s'')
        | (none, s'') => (none, s'')
      | (none, s') => (none, s') := by
  rw [List.mapM_cons, runOn_optionT_bind]
  generalize runOn (f x).run s = p
  rcases p with ⟨o, s'⟩
  cases o with
  | none => rfl
  | some b =>
    simp only
    rw [runOn_optionT_bind]
    generalize runOn (xs.mapM f).run s' = q
    rcases q with ⟨o', s''⟩
    cases o' <;> rfl

@[frflow_defs] theorem runOn_each {σ α β : Type} (xs : List α) (f : α → OptionT (StateM σ) β) (s : σ) :
    runOn (Races.each xs f).run s =
      ((runOn (xs.mapM (fun x => (f x).run)) s).1.mapM id, (runOn (xs.mapM (fun x => (f x).run)) s).2) := rfl

@[frflow_defs] theorem runOnE_each {σ ε α β : Type} (xs : List α) (f : α → OptionT (ExceptT ε (StateM σ)) β) (s : σ) :
    runOnE (Races.each xs f).run s = match runOnE (xs.mapM (fun x => (f x).run)) s with
      | (.ok os, s') => (.ok (os.mapM id), s')
      | (.error e, s') => (.error e, s') := by
  show runOnE ((xs.mapM (fun x => (f x).run)) >>= fun os => pure (os.mapM id)) s = _
  rw [runOnE_bind]
  generalize runOnE (xs.mapM (fun x => (f x).run)) s = p
  rcases p with ⟨r, s'⟩
  cases r <;> rfl

@[frflow_defs] theorem runOnE_cut {σ ε α : Type} (x : OptionT (ExceptT ε (StateM σ)) α) (s : σ) :
    runOnE (Races.cut x) s = match runOnE x.run s with
      | (.ok _, s') => (.ok (), s')
      | (.error e, s') => (.error e, s') := by
  show runOnE (x.run >>= fun _ => pure ()) s = _
  rw [runOnE_bind]
  generalize runOnE x.run s = p
  rcases p with ⟨r, s'⟩
  cases r <;> rfl
@[frflow_defs] theorem runOnE_optionT_pure {σ ε α : Type} (a : α) (s : σ) :
    runOnE (pure a : OptionT (ExceptT ε (StateM σ)) α).run s = (.ok (some a), s) := rfl
@[frflow_defs] theorem runOnE_optionT_bind {σ ε α β : Type} (x : OptionT (ExceptT ε (StateM σ)) α)
    (f : α → OptionT (ExceptT ε (StateM σ)) β) (s : σ) : runOnE (x >>= f).run s = match runOnE x.run s with
      | (.ok (some a), s') => runOnE (f a).run s'
      | (.ok none, s') => (.ok none, s')
      | (.error e, s') => (.error e, s') := by
  show runOnE (x.run >>= fun o => match o with | some a => (f a).run | none => pure none) s = _
  rw [runOnE_bind]
  generalize runOnE x.run s = p
  rcases p with ⟨r, s'⟩
  rcases r with e | o
  · rfl
  · cases o <;> rfl
@[frflow_defs] theorem runOnE_step {σ ε α : Type} [Races (ExceptT ε (StateM σ))] (x : ExceptT ε (StateM σ) α)
    (s : σ) : runOnE (Races.step x).run s = match runOnE (Races.leftWins : ExceptT ε (StateM σ) Bool) s with
      | (.ok true, s') => (.ok none, s')
      | (.ok false, s') => match runOnE x s' with
        | (.ok a, s'') => (.ok (some a), s'')
        | (.error e, s'') => (.error e, s'')
      | (.error e, s') => (.error e, s') := by
  show runOnE (Races.leftWins >>= fun b => if b then pure none else some <$> x) s = _
  rw [runOnE_bind]
  generalize runOnE (Races.leftWins : ExceptT ε (StateM σ) Bool) s = p
  rcases p with ⟨r, s'⟩
  rcases r with e | b
  · rfl
  · cases b
    · show runOnE (some <$> x) s' = _
      rw [runOnE_map]
      rfl
    · rfl
@[frflow_defs] theorem runOnE_optionT_throw {σ ε α : Type} (e : ε) (s : σ) :
    runOnE (throwThe ε e : OptionT (ExceptT ε (StateM σ)) α).run s = (.error e, s) := rfl
@[frflow_defs] theorem runOnE_optionT_tryCatch {σ ε α : Type} (x : OptionT (ExceptT ε (StateM σ)) α)
    (h : ε → OptionT (ExceptT ε (StateM σ)) α) (s : σ) :
    runOnE (tryCatchThe ε x h).run s = match runOnE x.run s with
      | (.ok a, s') => (.ok a, s')
      | (.error e, s') => runOnE (h e).run s' := by
  show runOnE (tryCatchThe ε x.run (fun e => (h e).run)) s = _
  rw [runOnE_tryCatch]
  generalize runOnE x.run s = p
  rcases p with ⟨r, s'⟩
  cases r <;> rfl
@[frflow_defs ↓] theorem runOnE_optionT_ite {σ ε α : Type} {c : Prop} {h : Decidable c}
    (x y : OptionT (ExceptT ε (StateM σ)) α) (s : σ) :
    runOnE (@ite _ c h x y).run s = @ite _ c h (runOnE x.run s) (runOnE y.run s) := by
  split <;> rfl
@[frflow_defs] theorem runOnE_optionT_mapM_nil {σ ε α β : Type} (f : α → OptionT (ExceptT ε (StateM σ)) β) (s : σ) :
    runOnE (([] : List α).mapM f).run s = (.ok (some []), s) := rfl
@[frflow_defs] theorem runOnE_optionT_mapM_cons {σ ε α β : Type} (f : α → OptionT (ExceptT ε (StateM σ)) β) (x : α)
    (xs : List α) (s : σ) : runOnE ((x :: xs).mapM f).run s = match runOnE (f x).run s with
      | (.ok (some b), s') => match runOnE (xs.mapM f).run s' with
        | (.ok (some bs), s'') => (.ok (some (b :: bs)), s'')
        | (.ok none, s'') => (.ok none, s'')
        | (.error e, s'') => (.error e, s'')
      | (.ok none, s') => (.ok none, s')
      | (.error e, s') => (.error e, s') := by
  rw [List.mapM_cons, runOnE_optionT_bind]
  generalize runOnE (f x).run s = p
  rcases p with ⟨r, s'⟩
  rcases r with e | o
  · rfl
  · cases o with
    | none => rfl
    | some b =>
      simp only
      rw [runOnE_optionT_bind]
      generalize runOnE (xs.mapM f).run s' = q
      rcases q with ⟨r', s''⟩
      rcases r' with e' | o'
      · rfl
      · cases o' <;> rfl

end FrFlow
