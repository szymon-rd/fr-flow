package frflow.testing.search

import frflow.core.analysis.Resolved
import frflow.core.consistency.{Defining, Picked}
import frflow.core.expr.{Expr, Exprs, Lambda, PrimOp}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{CallForm, CallForms}
import frflow.core.spec.Written.term
import frflow.core.term.Stated
import frflow.core.vocab.SymbolType
import frflow.eval.{Env, Fn, ScalaValue, Semantics}
import frflow.eval.run.Wiring
import frflow.testing.Case

/** A step whose proof does not go through, searched for a case that refutes it (today's `Refutation`): its one part a
  * claim fixing a Definition's result (`guard implies op(inputs) === e`), so `e` is an answer the claim allows; a
  * case where the claim fails with that answer, the Definition answering `e` everywhere (`consistency.Defining`), is
  * the candidate Lean is then asked to prove (`proof.layout.Refutes`). The cases are tried in order.
  */
object StepRefutation:
  def candidate(semantics: Semantics, r: Resolved, node: NodeId, cases: List[Case]): Option[Refuted] =
    val t = r.theory
    for
      part         <- Option(t.refinement.parts(node)).collect { case List(p) => p }
      (op, post)   <- t.node(part).flatMap(_.statement.call).collect { case CallForm.Call(o, p) => (o, p) }
      (e, picked)  <- fixed(post.value, op)
      rule         <- t.node(part).flatMap(_.statement.said)
      claim        <- t.node(node).flatMap(_.statement.said).map(CallForms.whole)
      ty           <- t.vocabulary.symbol(op).map(_.ty).collect { case SymbolType.Typed(x) => x }
      (wiring, witness) = (Wiring.onModels(semantics, t), Stated(Defining.of(rule.term, picked)))
      found        <- cases.find { c =>
        val env = Env.of(wiring.values(wiring.supplied(c.givens)))
        semantics.term(witness)(env).exists { answer =>
          val answering = Fn.of[AnyRef](post.value.arity)(args =>
            args.foldLeft(answer)((g, x) => Fn.call(Fn.ref(g), List(x))))
          semantics.lambda(claim).run(env.withSymbol(op, ScalaValue(answering)),
            c.inputs.zip(claim.value.params.map(_.ty)).map(semantics.literal)).exists(v => !Fn.bool(v))
        }
      }
    yield Refuted(claim.value.params.map(_.hint).zip(found.inputs), claim.value.params.map(_.ty), e, witness, ty)

  /** `e` of a claim's post `guard implies op(inputs) === e` or `op(inputs) === e` (written as a claim, the post is
    * over the call's inputs), `e` not mentioning the Definition.
    */
  def answerOf(post: Lambda, op: SymbolName): Option[Expr] = fixed(post, op).map(_._1)

  /** `e`, and on which side of the equation it is. */
  private def fixed(post: Lambda, op: SymbolName): Option[(Expr, Picked)] =
    val conclusion = post.body match
      case Expr.Prim(PrimOp.Implies, List(_, c), _) => c
      case other                                    => other
    val inputs = post.params.map(Expr.Var(_))
    def call(e: Expr): Boolean = e match
      case Expr.Apply(Expr.Sym(`op`, _), `inputs`, _) => true
      case _                                         => false
    conclusion match
      case Expr.Prim(PrimOp.Eq, List(c, a), _) if call(c) && !mentions(a, op) => Some(a -> Picked.Right(0))
      case Expr.Prim(PrimOp.Eq, List(a, c), _) if call(c) && !mentions(a, op) => Some(a -> Picked.Left(0))
      case _                                                                   => None

  private def mentions(e: Expr, op: SymbolName): Boolean =
    Exprs.all(e).exists { case Expr.Sym(`op`, _) => true; case _ => false }
