package frflow.core.analysis

import cats.syntax.all.*
import frflow.core.expr.{Exprs, Mentions}
import frflow.core.graph.Walk
import frflow.core.name.NodeId
import frflow.core.spec.Reliance
import frflow.core.{Failing, Theory}

/** A valid theory to its resolved relations, each program typed with the error it may fail with (`Failing`). There
  * are no definitions to choose among: a term is fixed by a `define` (owner §12).
  */
object Resolve:
  def apply(v: Valid): Resolved =
    val t = Failing.typed(v.theory)
    val ids = t.nodes.map(_.node.id)
    val relies = ids.map(id => id -> reliesOn(t, id)).toMap
    Resolved(t, ids.map(id => id -> constrainingCalled(t, Callees.of(t, id)).filterNot(_ == id)).toMap, relies,
      ids.map(id => id -> provenFrom(t, id, relies(id))).toMap)

  /** What a node's statement mentions, through the defines it calls. */
  def mentions(t: Theory, id: NodeId): Mentions =
    val own = t.node(id).toList.flatMap(_.statement.exprs).foldMap(Exprs.mentions)
    own |+| t.vocabulary.closure(own.defines).foldMap(d => Exprs.mentions(d.lambda.body))

  /** The statements constraining what the code calls, the code's own Definitions excepted. */
  def constrainingCalled(t: Theory, code: Option[Callees]): List[NodeId] = code.toList.flatMap { c =>
    val called = c.calls.symbols.filterNot(c.standsFor.contains).filter(Constrained.isFunction(t, _))
    called.flatMap(Constrained.statements(t, _)).distinct
  }

  /** What a node's proof of its code relies on, facts about what the code calls: the statements constraining a
    * callee, but the node itself, its ancestors (which rest on it), those about the code's own Definitions (proven of
    * the same code, not facts about a callee) and a callee fixing a word left open above.
    */
  def reliesOn(t: Theory, id: NodeId): List[NodeId] =
    val code = Callees.of(t, id)
    val own = code.toList.flatMap(_.standsFor.keys).toSet
    val above = t.refinement.ancestors(id).toSet
    constrainingCalled(t, code).filterNot(n => n == id || above(n) || Constrained.of(t, n).exists(own) ||
      leftOpenAndNamed(t, id)(n))

  /** What a node is proven from below it: of a node proven of code (`impl`), the parts it states, or with none what
    * its code relies on; of any other, its parts (`complete`).
    */
  def provenFrom(t: Theory, id: NodeId, relies: => List[NodeId]): List[NodeId] =
    val parts = t.refinement.parts(id)
    if Callees.of(t, id).isEmpty then parts
    else parts.filter(p => t.node(p).exists(_.statement.stated)) match
      case Nil    => relies
      case stated => stated

  /** The circles of proofs (`provenFrom`), each once in the theory's order: nodes each proven, through the others,
    * from itself. A circle of parts alone is the refinement's (`AboveItself`), not counted here.
    */
  def circles(t: Theory): List[List[NodeId]] =
    val ids = t.nodes.map(_.node.id)
    val below = ids.map(id => id -> provenFrom(t, id, reliesOn(t, id))).toMap.withDefaultValue(Nil)
    val reach = ids.map(id => id -> Walk.breadthFirst(below(id), identity)(below).toSet).toMap
    val circling = ids.filter(id => reach(id)(id) && !t.refinement.ancestors(id).contains(id))
    circling.map(id => circling.filter(m => reach(id)(m) && reach(m)(id))).distinct

  /** A callee fixing a word left open above, whose Definition the caller's statement names. */
  private def leftOpenAndNamed(t: Theory, caller: NodeId)(callee: NodeId): Boolean =
    t.node(callee).map(_.statement).exists(s => s.relied == Reliance.LeftOpen &&
      s.definition.exists(mentions(t, caller).symbols.contains))
