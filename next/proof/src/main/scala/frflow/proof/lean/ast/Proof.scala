package frflow.proof.lean.ast

/** How a generated theorem is proven: ` := rfl`; a term on the next line (` :=\n  Crm.N.Proofs.impl`); or tactics
  * (` := by\n  frflow_auto`). Tactic lines are the AST's one text: FrFlow's own fixed tactics, never built from a
  * model.
  */
enum Proof:
  case Rfl
  case Below(term: LExpr)
  case Tactics(lines: List[String])
