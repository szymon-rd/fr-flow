import FrFlow.Attr

/-! The tactics FrFlow's generated theorems of the theory as a whole use (r43 revision 14): a consistency or vacuity
statement met by the witnesses FrFlow derived (`frflow_witness`, after the anonymous constructor gave them), and an
example checked against the claims (`frflow_example`, a try within a budget). Each is fixed text of FrFlow's. -/

/-- What is left once the witnesses are given: the statements at them, unfolded and closed by rewriting,
deciding, or arithmetic. -/
macro "frflow_witness" : tactic =>
  `(tactic| first
    | (intros; rfl)
    | (simp only [frflow_defs]; intros; rfl)
    | (simp only [frflow_defs]; done)
    | (simp [frflow_defs]; done)
    | (simp [frflow_defs]; decide)
    | decide)

/-- An example from the claims about the Definitions it mentions, given as hypotheses: the first that rewrites the
Definition so that its guards and what is left are decided. -/
syntax "frflow_example" (ppSpace colGt ident)+ : tactic
macro_rules
  | `(tactic| frflow_example $h) => `(tactic| (rw [$h:ident] <;> simp [frflow_defs]))
  | `(tactic| frflow_example $h $hs*) =>
    `(tactic| first | (rw [$h:ident] <;> simp [frflow_defs]; done) | frflow_example $hs*)
