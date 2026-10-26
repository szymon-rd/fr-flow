package frflow.eval.run

import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.core.spec.Statement
import frflow.core.Theory
import frflow.eval.{Applied, Denote, Env, Fn, ScalaValue}

/** An invariant a contract keeps: each pair its view lists of a call meets the invariant's rule. */
final case class Kept(invariant: NodeId, view: Applied, rule: Applied):
  def broken(call: List[ScalaValue], env: Env): Option[Broken] = view.run(env, call) match
    case Left(e)      => Some(Broken.NotEvaluated(e))
    case Right(pairs) =>
      val holds = Fn.pairs(pairs).forall((x, y) => rule.run(env, List(x, y)).exists(Fn.bool))
      Option.unless(holds)(Broken.Invariant(invariant))

object Kept:
  def of(denote: Denote, t: Theory, contract: NodeId): List[Kept] = t.edges.collect {
    case Edge.Keeps(`contract`, i, view) => (i, view)
  }.flatMap((i, view) => t.node(i).map(_.statement).collect { case Statement.Invariant(rule, _) =>
    Kept(i, denote.lambda(view.value), denote.lambda(rule.value))
  })
