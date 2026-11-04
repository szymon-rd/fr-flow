package frflow.core.checking

import frflow.core.analysis.Constrained
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{CallForm, NodeKind}
import frflow.core.Theory

/** A piece of behaviour assumed, checked where it can be: a promise about a Definition with plain Scala, known only
  * by the assumptions about it (an outside system's), its Scala tested against them where a case can be evaluated
  * (`Assumption`); or, where its model's generated runs cannot evaluate it (it is not read as a run of the operation,
  * or its post has no Scala value), trusted, not tested (`Untested`).
  */
enum Assumed:
  case Assumption
  case Untested(operations: List[SymbolName])

object Assumed:
  /** The operations known only by assumptions an assumption is about that its model's generated runs cannot check it
    * against (`AssumedRuns` reads only a run of one of them whose post has a Scala value).
    */
  def untested(t: Theory, id: NodeId): List[SymbolName] =
    t.node(id).filter(_.statement.kind == NodeKind.Assumption).toList.flatMap { n =>
      val run = n.statement.call.collect { case CallForm.Run(op, post, _) if Evaluable.of(t, post.value.body) => op }
      Constrained.of(t, id).filter(t.vocabulary.isAssumed).distinct.filterNot(run.contains)
    }
