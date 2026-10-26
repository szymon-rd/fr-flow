package frflow.testing.search

import frflow.core.analysis.Resolved
import frflow.core.expr.{Expr, Exprs, Lambda, PrimOp}
import frflow.core.name.{NodeId, SymbolName}
import frflow.eval.Semantics
import frflow.testing.Case

/** A step whose proof does not go through, searched for a case that refutes it (today's `Refutation`): its one part a
  * claim fixing a Definition's result (`guard implies op(inputs) === e`), so `e` is an answer the claim allows; a
  * generated case where the claim fails with that answer is the candidate Lean is then asked to prove
  * (`proof.layout.Refutes`).
  */
object StepRefutation:
  def candidate(semantics: Semantics, r: Resolved, node: NodeId, cases: List[Case]): Option[Refuted] = ???

  /** `e` of a claim's post `guard implies op(inputs) === e` or `op(inputs) === e` (written as a claim, the post is
    * over the call's inputs), `e` not mentioning the Definition.
    */
  def answerOf(post: Lambda, op: SymbolName): Option[Expr] =
    val conclusion = post.body match
      case Expr.Prim(PrimOp.Implies, List(_, c), _) => c
      case other                                    => other
    val inputs = post.params.map(Expr.Var(_))
    def call(e: Expr): Boolean = e match
      case Expr.Apply(Expr.Sym(`op`, _), `inputs`, _) => true
      case _                                         => false
    conclusion match
      case Expr.Prim(PrimOp.Eq, List(c, a), _) if call(c) && !mentions(a, op) => Some(a)
      case Expr.Prim(PrimOp.Eq, List(a, c), _) if call(c) && !mentions(a, op) => Some(a)
      case _                                                                   => None

  private def mentions(e: Expr, op: SymbolName): Boolean =
    Exprs.all(e).exists { case Expr.Sym(`op`, _) => true; case _ => false }
