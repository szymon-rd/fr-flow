import FrFlow.Attr

/-!
# FrFlow kernel: proof automation

`frflow_auto` is the tactic FrFlow tries first on every generated obligation.
It unfolds all generated definitions, simplifies, and closes what remains with
`grind`, or with function extensionality and case splits on `if`. Obligations
it does not close are left to authored proofs (`Proofs/<Theory>/<Layer>.lean`).

The tactic only produces proofs; the kernel checks them. A wrong automation
step cannot make a false obligation pass.
-/

/-- Try to prove a generated obligation automatically. -/
syntax "frflow_auto" : tactic

macro_rules
  | `(tactic| frflow_auto) => `(tactic| (
      intros
      try simp_all only [frflow_defs]
      try simp_all
      all_goals first
        | done
        | grind
        | ((repeat (apply funext; intro)) <;> (try split) <;> simp_all)
        | ((repeat (apply funext; intro)) <;> (try split) <;> simp_all <;> grind)
        | fail "frflow_auto found no proof; prove this obligation in the node's proof file"))
