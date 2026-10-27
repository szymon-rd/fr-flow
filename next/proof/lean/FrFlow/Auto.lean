import FrFlow.Attr
import FrFlow.Faults

/-!
`frflow_auto`: the tactic tried first on every link obligation. It unfolds the
generated definitions, simplifies (twice: what `simp` makes of a step may be one the
definitions' lemmas compute), and closes what remains with `grind` (after splitting
conjunctions under quantifiers, when `grind` alone fails).
-/

syntax "frflow_auto" : tactic

macro_rules
  | `(tactic| frflow_auto) => `(tactic| (
      intros
      try simp_all only [frflow_defs]
      try simp_all
      -- what `simp` made of a step (a traverse of a literal list, `pure [...]`) is a run FrFlow's lemmas compute
      try simp_all only [frflow_defs]
      try simp_all
      all_goals first
        | done
        | grind
        | (simp only [forall_and] at *; grind)
        -- maps and sets are functions: equal when equal at every key
        | (simp only [funext_iff] at *; grind)
        -- a run that may fail: each case of the faults it takes
        | (frflow_faults; all_goals (try simp_all); all_goals (first | done | grind))
        | fail "frflow_auto found no proof; prove this obligation in the node's proof file"))

namespace FrFlow
open Lean Elab Tactic

/-- `frflow_eval`: decides an example. `simp` computes it; a map or a set (a function) is compared
key by key, splitting on the keys the example names. An example `simp` computes to `False` is
false (simp's rewrites keep the goal's meaning), so nothing else is tried on it: half of the
examples' theorems are opposites that do not hold, and `grind` on each takes most of their time. -/
elab "frflow_eval" : tactic => do
  let start ← saveState
  let computed ← try
      evalTactic (← `(tactic| simp [frflow_defs]))
      if (← getGoals).isEmpty then pure (some true)
      else if (← instantiateMVars (← getMainTarget)).isConstOf ``False then pure (some false)
      else pure none
    catch _ => pure none
  match computed with
  | some true => pure ()
  | some false => throwError "frflow_eval: simp computes this example to False"
  | none =>
    start.restore
    evalTactic (← `(tactic| first
      | (simp [frflow_defs, funext_iff]; done)
      | (simp [frflow_defs, funext_iff] <;> grind)))

end FrFlow
