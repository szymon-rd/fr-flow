import FrFlow.Attr

/-! The tactic FrFlow's generated theorems of the theory as a whole use: a consistency or vacuity statement met by the
witnesses FrFlow derived (`frflow_witness`, after the anonymous constructor gave them). Fixed text of FrFlow's. -/

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
