import FrFlow.Attr
import FrFlow.Faults

/-!
`frflow_auto`: the tactic tried first on every link obligation. It unfolds the
generated definitions, simplifies, and closes what remains with `grind` (splitting
conjunctions under quantifiers first, if that is what it takes). It only
produces proofs; Lean checks them.
-/

syntax "frflow_auto" : tactic

macro_rules
  | `(tactic| frflow_auto) => `(tactic| (
      intros
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

/-- `frflow_eval`: decides an example. `simp` computes it; a map or a set (a function) is compared
key by key, splitting on the keys the example names. -/
syntax "frflow_eval" : tactic

macro_rules
  | `(tactic| frflow_eval) => `(tactic| (
      first
        | (simp [frflow_defs]; done)
        | (simp [frflow_defs, funext_iff]; done)
        | (simp [frflow_defs, funext_iff] <;> grind)))
