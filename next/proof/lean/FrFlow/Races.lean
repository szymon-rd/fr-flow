import FrFlow.Flow

/-!
Races. A program that races two branches runs one of them: the scheduler's choice of the winner,
which Lean leaves open. A run takes it from the world's `races`, the next of them in turn (`true`:
the left wins), the left when none is left, as the Scala tests' sequential runs do; a statement
holds of every world, so of every choice.
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

/-- In a program that may fail, the choice is made as in one that may not. -/
instance {ε : Type} {m : Type → Type} [Monad m] [Races m] : Races (ExceptT ε m) := ⟨ExceptT.lift Races.leftWins⟩

@[frflow_defs] theorem Races.leftWins_exceptT {ε : Type} {m : Type → Type} [Monad m] [Races m] :
    (Races.leftWins : ExceptT ε m Bool) = ExceptT.lift Races.leftWins := rfl

end FrFlow
