import FrFlow.Flow

/-!
Time, as Cats Effect models it (owner §47). The clock's state is the time now, a field of the World; steps of code
take no time of their own. The world moves the time on: between runs (`elapse`, the world's own step), after each
of the clock's steps in a run (`tick`: the next of the world's `ticks`, none left: no time; what passes before a
run's first look at the clock is the world's step before it), and at a wait's end, by at least its seconds. Every move the world makes is one the schedules allow (`allows`, a trusted fact restricting the
world's steps): a move they do not allow is not taken, as no run the facts trust makes it. Waits at once are read as
two points: where the sides start, and the time reached at each end (`Waits.reach`): two ends commute, so waits at
once take the longest, not the sum.
-/

noncomputable section
open Classical

namespace FrFlow

/-- The time moved to `t`, where the schedules allow it; else as it was. -/
def Clock.move {σ : Type} (put : σ → Int → σ) (allows : σ → Int → Prop) (t : Int) (s : σ) : σ :=
  if allows s t then put s t else s

/-- The world moving the time on by the next of its ticks (none left: by nothing), where the schedules allow. -/
def Clock.ticked {σ : Type} (ticks : σ → List Nat) (putTicks : σ → List Nat → σ) (clock : σ → Int)
    (put : σ → Int → σ) (allows : σ → Int → Prop) (s : σ) : σ :=
  match ticks s with
    | d :: ds => Clock.move put allows (clock s + d) (putTicks s ds)
    | [] => s

/-- A step of the clock, then the world moving the time on by the next of its ticks. -/
def Clock.tick {σ α : Type} (ticks : σ → List Nat) (putTicks : σ → List Nat → σ) (clock : σ → Int)
    (put : σ → Int → σ) (allows : σ → Int → Prop) (x : StateM σ α) : StateM σ α :=
  fun s => pure ((runOn x s).1, Clock.ticked ticks putTicks clock put allows (runOn x s).2)

/-- A step moving the time on (a wait's end, the world's own step), the move taken where the schedules allow it. -/
def Clock.guard {σ α : Type} (clock : σ → Int) (put : σ → Int → σ) (allows : σ → Int → Prop) (x : StateM σ α) :
    StateM σ α :=
  fun s => pure ((runOn x s).1, Clock.move put allows (clock (runOn x s).2) s)

/-- A wait's end at once with others: the time reaches at least the sides' start plus the wait's seconds. -/
def Clock.reach {σ : Type} (clock : σ → Int) (put : σ → Int → σ) (allows : σ → Int → Prop) (start d : Int) :
    StateM σ Unit :=
  fun s => pure ((), Clock.move put allows (max (clock s) (start + max d 0)) s)

/-- What a program waiting at once asks of its monad: the end of a wait beside others. -/
class Waits (m : Type → Type) where
  reach : Int → Int → m Unit

/-- In a program that may fail, a wait's end is as in one that may not. -/
instance {ε : Type} {m : Type → Type} [Monad m] [Waits m] : Waits (ExceptT ε m) :=
  ⟨fun a b => ExceptT.lift (Waits.reach a b)⟩

@[frflow_defs] theorem Waits.reach_exceptT {ε : Type} {m : Type → Type} [Monad m] [Waits m] (a b : Int) :
    (Waits.reach a b : ExceptT ε m Unit) = ExceptT.lift (Waits.reach a b) := rfl

@[frflow_defs] theorem runOn_tick {σ α : Type} (ticks : σ → List Nat) (putTicks : σ → List Nat → σ)
    (clock : σ → Int) (put : σ → Int → σ) (allows : σ → Int → Prop) (x : StateM σ α) (s : σ) :
    runOn (Clock.tick ticks putTicks clock put allows x) s =
      ((runOn x s).1, Clock.ticked ticks putTicks clock put allows (runOn x s).2) := rfl

@[frflow_defs] theorem runOn_guard {σ α : Type} (clock : σ → Int) (put : σ → Int → σ) (allows : σ → Int → Prop)
    (x : StateM σ α) (s : σ) :
    runOn (Clock.guard clock put allows x) s =
      ((runOn x s).1, Clock.move put allows (clock (runOn x s).2) s) := rfl

@[frflow_defs] theorem runOn_reach {σ : Type} (clock : σ → Int) (put : σ → Int → σ) (allows : σ → Int → Prop)
    (start d : Int) (s : σ) :
    runOn (Clock.reach clock put allows start d) s =
      ((), Clock.move put allows (max (clock s) (start + max d 0)) s) := rfl

/-- With no schedule, every move is taken. -/
@[frflow_defs] theorem Clock.move_free {σ : Type} (put : σ → Int → σ) (t : Int) (s : σ) :
    Clock.move put (fun _ _ => True) t s = put s t := by
  simp [Clock.move]

/-- A part of the state the clock's moves do not put is as it was: how the World's other fields read through the
time passing (the generated `ticked_<field>` and `move_<field>` lemmas). -/
theorem Clock.move_other {σ τ : Type} (get : σ → τ) (put : σ → Int → σ) (allows : σ → Int → Prop) (t : Int) (s : σ)
    (h : ∀ s t, get (put s t) = get s) : get (Clock.move put allows t s) = get s := by
  unfold Clock.move
  split
  · exact h s t
  · rfl

theorem Clock.ticked_other {σ τ : Type} (get : σ → τ) (ticks : σ → List Nat) (putTicks : σ → List Nat → σ)
    (clock : σ → Int) (put : σ → Int → σ) (allows : σ → Int → Prop) (s : σ)
    (h₁ : ∀ s ds, get (putTicks s ds) = get s) (h₂ : ∀ s t, get (put s t) = get s) :
    get (Clock.ticked ticks putTicks clock put allows s) = get s := by
  unfold Clock.ticked
  split
  · rw [Clock.move_other get put allows _ _ h₂, h₁]
  · rfl

/-- A move forwards never takes the time back. -/
theorem Clock.move_le {σ : Type} (clock : σ → Int) (put : σ → Int → σ) (allows : σ → Int → Prop) (t : Int) (s : σ)
    (hput : ∀ s t, clock (put s t) = t) (h : clock s ≤ t) : clock s ≤ clock (Clock.move put allows t s) := by
  unfold Clock.move
  split
  · rw [hput]; exact h
  · exact Int.le_refl _

end FrFlow
