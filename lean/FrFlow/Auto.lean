import FrFlow.Attr

/-!
`frflow_auto`: the tactic tried first on every link obligation. It unfolds the
generated definitions, simplifies, and closes what remains with `grind`. It only
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
        | fail "frflow_auto found no proof; prove this obligation in the node's proof file"))
