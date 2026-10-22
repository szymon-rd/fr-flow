/-!
State machines. A root of the shape `inv init ∧ ∀ s e, inv s → inv (step s e)` states an
inductive invariant: `always` lifts it to every state the machine reaches from `init`.
A run is `es.foldl step init`. `simulates` and its variants relate the states of one machine to
those of another (an abstraction), or to the history of events that led to them (`tracks`).
-/

namespace FrFlow

/-- A step that keeps an invariant keeps it in every state reached from a state that has it. -/
theorem always {S E : Type} (step : S → E → S) (inv : S → Prop) (init : S)
    (h0 : inv init) (h : ∀ s e, inv s → inv (step s e)) : ∀ es : List E, inv (es.foldl step init) := by
  intro es
  induction es generalizing init with
  | nil => simpa using h0
  | cons e es ih => simpa using ih (step init e) (h init e h0)

/-- The state after `es ++ [e]` is `e` applied to the state after `es` (rewrite with it to reason
about the last event of a run). -/
theorem run_snoc {S E : Type} (step : S → E → S) (init : S) (es : List E) (e : E) :
    (es ++ [e]).foldl step init = step (es.foldl step init) e := by
  simp

/-- Relational simulation: when `R` relates the initial states and every step on related states
gives related states, the states reached by the same events are related. Use it when the
correspondence needs an invariant of either machine (put the invariant into `R`). -/
theorem simulates_rel {S A E : Type} {step : S → E → S} {astep : A → E → A} {R : S → A → Prop}
    {init : S} {ainit : A}
    (h0 : R init ainit) (h : ∀ s a e, R s a → R (step s e) (astep a e)) :
    ∀ es : List E, R (es.foldl step init) (es.foldl astep ainit) := by
  intro es
  induction es generalizing init ainit with
  | nil => simpa using h0
  | cons e es ih => simpa using ih (h init ainit e h0)

/-- Simulation: if the abstraction `α` of a step is the abstract step of the abstraction, and the
initial states correspond, then the abstraction of every run is the abstract run of the same events.
Use it when a node describes a machine by a simpler one (its state seen through `α`). -/
theorem simulates {S A E : Type} {step : S → E → S} {astep : A → E → A} {α : S → A}
    {init : S} {ainit : A}
    (h0 : α init = ainit) (h : ∀ s e, α (step s e) = astep (α s) e) :
    ∀ es : List E, α (es.foldl step init) = es.foldl astep ainit :=
  simulates_rel (R := fun s a => α s = a) h0 (fun s _ e hs => hs ▸ h s e)

/-- Simulation under an invariant: as `simulates`, but the step need only mirror the abstract step
on states meeting `inv`, an invariant that holds initially and that every step keeps. -/
theorem simulates_of_inv {S A E : Type} {step : S → E → S} {astep : A → E → A} {α : S → A}
    {inv : S → Prop} {init : S} {ainit : A}
    (h0 : α init = ainit) (hi0 : inv init) (hi : ∀ s e, inv s → inv (step s e))
    (h : ∀ s e, inv s → α (step s e) = astep (α s) e) :
    ∀ es : List E, α (es.foldl step init) = es.foldl astep ainit := fun es =>
  (simulates_rel (R := fun s a => inv s ∧ α s = a) ⟨hi0, h0⟩
    (fun s _ e ⟨hs, ha⟩ => ⟨hi s e hs, ha ▸ h s e hs⟩) es).2

/-- Tracking a history: when `R` relates the initial state to the empty history and each step
extends the relation by its event, every state reached is related to the events that reached it.
Use it when a node describes the state by its history ("the sessions are the sign-ins not yet
signed out"); put any invariant the step needs into `R`. -/
theorem tracks {S E : Type} {step : S → E → S} {R : S → List E → Prop} {init : S}
    (h0 : R init []) (h : ∀ s es e, R s es → R (step s e) (es ++ [e])) :
    ∀ es : List E, R (es.foldl step init) es := by
  have : ∀ es s pre, R s pre → R (es.foldl step s) (pre ++ es) := by
    intro es
    induction es with
    | nil => intro s pre hs; simpa using hs
    | cons e es ih => intro s pre hs; simpa using ih (step s e) (pre ++ [e]) (h s pre e hs)
  intro es
  simpa using this es init [] h0

/-- Tracking a history by an abstraction: if `α` of the initial state is `H []` and a step by `e`
takes a state whose `α` is `H es` to one whose `α` is `H (es ++ [e])`, then `α` of the state
reached by `es` is `H es`. -/
theorem tracks_eq {S A E : Type} {step : S → E → S} {α : S → A} {H : List E → A} {init : S}
    (h0 : α init = H []) (h : ∀ s es e, α s = H es → α (step s e) = H (es ++ [e])) :
    ∀ es : List E, α (es.foldl step init) = H es :=
  tracks (R := fun s es => α s = H es) h0 h

end FrFlow
