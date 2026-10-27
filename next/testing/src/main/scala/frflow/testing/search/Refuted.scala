package frflow.testing.search

import frflow.core.expr.{Expr, Value}
import frflow.core.term.Stated
import frflow.core.ty.Ty

/** A case refuting a step: the claim's inputs, each named, and their types; the answer the part's claim gives on them
  * (`e` of `op(inputs) === e`); and that answer as the Definition answering it everywhere (`witness`, of the
  * Definition's type `ty`), which Lean is given to prove the step false (`proof.layout.RefutesModule`).
  */
final case class Refuted(inputs: List[(String, Value)], types: List[Ty], answer: Expr, witness: Stated[?], ty: Ty)
