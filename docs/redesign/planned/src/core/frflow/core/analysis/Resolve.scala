package frflow.core.analysis

import cats.syntax.all.*
import frflow.core.expr.{Exprs, Mentions}
import frflow.core.name.NodeId
import frflow.core.spec.Reliance
import frflow.core.Theory

/** A valid theory to its resolved relations. There are no definitions to choose among: a term is fixed by a `define`
  * (owner §12).
  */
object Resolve:
  def apply(v: Valid): Resolved =
    val t = v.theory
    val ids = t.nodes.map(_.node.id)
    val calls = ids.map(id => id -> constrainingCalled(t, Callees.of(t, id)).filterNot(_ == id)).toMap
    Resolved(t, calls, ids.map(id => id -> calls(id).filterNot(leftOpenAndNamed(t, id))).toMap)

  /** What a node's statement mentions, through the defines it calls. */
  def mentions(t: Theory, id: NodeId): Mentions =
    val own = t.node(id).toList.flatMap(_.statement.exprs).foldMap(Exprs.mentions)
    own |+| t.vocabulary.closure(own.defines).foldMap(d => Exprs.mentions(d.lambda.body))

  /** The statements constraining what the code calls, the code's own Definitions excepted. */
  def constrainingCalled(t: Theory, code: Option[Callees]): List[NodeId] = code.toList.flatMap { c =>
    val called = c.calls.symbols.filterNot(c.standsFor.contains).filter(Constrained.isFunction(t, _))
    called.flatMap(Constrained.statements(t, _)).distinct
  }

  /** A callee fixing a word left open above, whose Definition the caller's statement names. */
  private def leftOpenAndNamed(t: Theory, caller: NodeId)(callee: NodeId): Boolean =
    t.node(callee).map(_.statement).exists(s => s.relied == Reliance.LeftOpen &&
      s.definition.exists(mentions(t, caller).symbols.contains))
