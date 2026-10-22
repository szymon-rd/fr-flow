/-!
State machines. A root of the shape `inv init ∧ ∀ s e, inv s → inv (step s e)` states an
inductive invariant: `always` lifts it to every state the machine reaches from `init`.
-/

namespace FrFlow

/-- A step that keeps an invariant keeps it in every state reached from a state that has it. -/
theorem always {S E : Type} (step : S → E → S) (inv : S → Prop) (init : S)
    (h0 : inv init) (h : ∀ s e, inv s → inv (step s e)) : ∀ es : List E, inv (es.foldl step init) := by
  intro es
  induction es generalizing init with
  | nil => simpa using h0
  | cons e es ih => simpa using ih (step init e) (h init e h0)

end FrFlow
