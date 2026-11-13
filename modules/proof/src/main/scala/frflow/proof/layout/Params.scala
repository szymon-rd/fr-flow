package frflow.proof.layout

import frflow.proof.prover.ast.*
import frflow.proof.prover.ast.Tree.into
import frflow.proof.prover.term.Silent

/** The names a statement binds, in order, for a proof `fun` over it: each `∀`'s binders, then a name from `hyps` for
  * each hypothesis stated by an arrow.
  */
object Params:
  def of(e: LExpr, hyps: List[String]): List[ProverName] = e.into(Bound)(hyps)

  /** `fun x₁ … => body`, or the body alone over no names. */
  def lambda(names: List[ProverName], body: LExpr): LExpr =
    if names.isEmpty then body else LExpr.Fun(names.map(LBinder.Bare(_)), body)

  /** A statement's top, as what it binds given the names its hypotheses take: a `∀`, what is in parentheses and
    * an arrow say; every other form binds nothing.
    */
  private type Binds = List[String] => List[ProverName]
  private object Bound extends Silent[Binds](_ => Nil):
    override def forall(params: List[Binding[Binds]], body: Binds): Binds =
      hyps => params.flatMap(_.bound) ++ body(hyps)
    override def paren(inner: Binds): Binds = inner
    override def infix(op: LOp, left: Binds, right: Binds): Binds = hyps =>
      if op == LOp.Arrow && hyps.nonEmpty then Names.builtin(hyps.head) :: right(hyps.tail) else Nil
