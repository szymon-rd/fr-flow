package frflow.core.analysis

import frflow.core.code.{Code, Realizes}
import frflow.core.name.{DefName, NodeId}
import frflow.core.spec.Statement
import frflow.core.Theory

/** How the code under a node is shown to meet what is decided, piece by piece. */
final case class Shown(proven: Option[DefName], tested: List[Tested], assumed: List[Assumed])

object Shown:
  /** One function of the statement, the attachment and the realizations: the only place this is decided. */
  def of(t: Theory, id: NodeId): Shown =
    val attached = t.code.attached.get(id).map(_.code)
    val realized = t.code.realized.get(id).toList.flatMap(_.toList).zipWithIndex
    Shown(attached.flatMap(_.proven),
      attached.toList.flatMap(tested) ++ realized.collect { case (r, i) if r.how == Realizes.Own => Tested.Own(i) },
      assumedPromise(t, id) ++ realized.collect { case (r, i) if r.how == Realizes.Outside => Assumed.Outside(i) })

  private def tested(c: Code) = c match
    case Code.ProvenBeside(d, _) => List(Tested.Beside(d))
    case Code.Tested(_, _)       => List(Tested.Plain)
    case _                       => Nil

  private def assumedPromise(t: Theory, id: NodeId) =
    t.node(id).map(_.statement).collect { case Statement.AssumedCall(_, _) => Assumed.Promise }.toList
