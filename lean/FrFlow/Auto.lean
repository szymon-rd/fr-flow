import FrFlow.Kernel

/-!
`frflow_auto`: the tactic tried first on every obligation. It unfolds the
generated definitions, simplifies, and closes what remains with `grind`. It only
produces proofs; Lean checks them.
-/

syntax "frflow_auto" : tactic

/-- Case analysis of a step hypothesis: unfold it and split every `match` and `if` in it. -/
syntax "frflow_cases " ident : tactic

macro_rules
  | `(tactic| frflow_cases $h) => `(tactic| (
      simp only [frflow_defs] at $h:ident
      repeat' split at $h:ident))

macro_rules
  | `(tactic| frflow_auto) => `(tactic| (
      intros
      try simp_all only [frflow_defs]
      try simp_all
      all_goals first
        | done
        | grind
        | (split <;> simp_all <;> grind)
        | fail "frflow_auto found no proof; prove this obligation in the node's proof file"))
