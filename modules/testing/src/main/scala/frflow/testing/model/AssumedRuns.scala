package frflow.testing.model

import frflow.core.Theory
import frflow.core.code.Values
import frflow.core.name.{ModelName, NodeId, SymbolName}
import frflow.core.spec.{CallForm, NodeKind}
import frflow.core.term.World
import frflow.eval.{Applied, Env, Fn, ScalaValue, Semantics}
import frflow.eval.run.Wiring

/** What is assumed of the operations known only by assumptions (G2, owner §36: "tested against them where
  * possible, trusted otherwise"): each assumption read as a run of one of them (`CallForm.Run`), its post over the
  * call's inputs, its result and the world before and after, compiled once. A generated run checks each call of the
  * operation's Scala against them; an assumption read otherwise, or whose post has no Scala value on a case, is
  * trusted there.
  */
final class AssumedRuns(posts: Map[SymbolName, List[(NodeId, Applied)]], values: Values):
  /** The assumptions a call breaks: given its inputs, its result, and its model's state before and after it. */
  def broken(op: SymbolName, model: ModelName)(args: List[ScalaValue], result: ScalaValue, states: (Any, Any))
      : List[NodeId] =
    val (before, after) = (world(model, states._1), world(model, states._2))
    posts.getOrElse(op, Nil).collect {
      case (id, post) if post.run(Env.of(values), args ++ List(result, before, after)).exists(v => !Fn.bool(v)) => id
    }

  private def world(m: ModelName, state: Any): ScalaValue = ScalaValue(World.of(Map(m -> state)))

object AssumedRuns:
  val none: AssumedRuns = AssumedRuns(Map.empty, Values.none)

  def of(semantics: Semantics, t: Theory): AssumedRuns =
    val read = t.nodes.map(_.node).filter(_.statement.kind == NodeKind.Assumption).flatMap(n =>
      n.statement.call.collect { case CallForm.Run(op, post, _) if t.vocabulary.isAssumed(op) =>
        op -> (n.id -> semantics.lambda(post)) })
    AssumedRuns(read.groupMap(_._1)(_._2), Wiring.onModels(semantics, t).values(Values.none))
