package frflow.core.analysis

import cats.syntax.all.*
import frflow.core.expr.{Exprs, Mentions}
import frflow.core.graph.Walk
import frflow.core.name.NodeId
import frflow.core.spec.{NodeKind, Reliance}
import frflow.core.{Failing, Theory}
import frflow.core.typing.IrCheck

/** A valid theory to its resolved relations, each program typed with the error it may fail with (`Failing`). There
  * are no definitions to choose among: a term is fixed by a `define` (owner §12).
  */
object Resolve:
  def apply(v: Valid): Resolved =
    val t = IrCheck.checked(Failing.typed(v.theory))
    val ids = t.nodes.map(_.node.id)
    val relies = ids.map(id => id -> reliesOn(t, id)).toMap
    Resolved(t, ids.map(id => id -> constrainingCalled(t, SaysWhat.checkedAgainst(t, id)).filterNot(_ == id)).toMap,
      relies,
      ids.map(id => id -> provenFrom(t, id, relies(id))).toMap)

  /** What a node's statement mentions, through the defines it calls. */
  def mentions(t: Theory, id: NodeId): Mentions =
    val own = t.node(id).toList.flatMap(_.statement.exprs).foldMap(Exprs.mentions)
    own |+| t.vocabulary.closure(own.defines).foldMap(d => Exprs.mentions(d.lambda.body))

  /** The statements constraining what the code calls, the code's own Definitions excepted, and those saying what a
    * Declaration is (nothing is proven of the code from them). An operation known only by assumptions is called as a
    * step: what is assumed of it, its assumptions only, is what a step calling it rests on (G2); a claim about it is
    * proven from them, so taking it too could prove it from itself.
    */
  def constrainingCalled(t: Theory, code: Option[Callees]): List[NodeId] = code.toList.flatMap { c =>
    val called = c.calls.symbols.filterNot(s => c.standsFor.contains(s) || t.vocabulary.isAssumed(s))
      .filter(Constrained.isFunction(t, _)).flatMap(Constrained.statements(t, _))
    val assumed = c.calls.operations.filter(t.vocabulary.isAssumed).flatMap(Constrained.assumptions(t, _))
    (called ++ assumed).distinct.filterNot(SaysWhat.is(t, _))
  }

  /** What is assumed of the operations known only by assumptions that a node's statement or the code it is checked
    * against reaches (G2): their assumptions, a hypothesis of every proof of it, never a claim about one.
    */
  def assumedOf(t: Theory, id: NodeId): List[NodeId] =
    def about(h: NodeId) = t.node(h).exists(_.statement.kind == NodeKind.Assumption) &&
      Constrained.of(t, h).exists(t.vocabulary.isAssumed)
    val direct = Constrained.of(t, id).filter(t.vocabulary.isAssumed).flatMap(Constrained.assumptions(t, _))
    Option.when(t.node(id).exists(_.statement.kind != NodeKind.Assumption))(reliesOn(t, id).filter(about) ++ direct)
      .toList.flatten.distinct.filterNot(_ == id)

  /** What a node's proof rests on below it, what its `complete` or `impl` takes: what it is proven from, and what is
    * assumed of the operations known only by assumptions it or its code reaches.
    */
  def below(t: Theory, id: NodeId): List[NodeId] =
    (provenFrom(t, id, reliesOn(t, id)) ++ assumedOf(t, id)).distinct

  /** What a node's proof of its code relies on, facts about what the code calls: the statements constraining a
    * callee, but the node itself, its ancestors (which rest on it), its descendants (its own parts, which rest on it
    * and are decided after it), those about the code's own Definitions (proven of the same code, not facts about a
    * callee), a callee fixing a word left open above, and the rules (Lean has each of every value already).
    */
  def reliesOn(t: Theory, id: NodeId): List[NodeId] =
    val code = SaysWhat.checkedAgainst(t, id)
    val own = code.toList.flatMap(_.standsFor.keys).toSet
    val related = t.refinement.ancestors(id).toSet ++ t.refinement.nodes.map(_.id)
      .filter(t.refinement.ancestors(_).contains(id))
    constrainingCalled(t, code).filterNot(n => n == id || related(n) || Constrained.of(t, n).exists(own) ||
      leftOpenAndNamed(t, id)(n) || t.node(n).exists(_.statement.rule))

  /** What a node is proven from below it: of a node proven of code (`impl`), the parts it states, or with none what
    * its code relies on; of any other, its parts (`complete`).
    */
  def provenFrom(t: Theory, id: NodeId, relies: => List[NodeId]): List[NodeId] =
    val parts = t.refinement.parts(id)
    if SaysWhat.checkedAgainst(t, id).isEmpty then parts
    else parts.filter(p => t.node(p).exists(_.statement.stated)) match
      case Nil    => relies
      case stated => stated

  /** The circles of proofs (`below`), each once in the theory's order: nodes each proven, through the others, from
    * itself. A circle of parts alone is the refinement's (`AboveItself`), not counted here.
    */
  def circles(t: Theory): List[List[NodeId]] =
    val ids = t.nodes.map(_.node.id)
    val below = ids.map(id => id -> Resolve.below(t, id)).toMap.withDefaultValue(Nil)
    val reach = ids.map(id => id -> Walk.breadthFirst(below(id), identity)(below).toSet).toMap
    val circling = ids.filter(id => reach(id)(id) && !t.refinement.ancestors(id).contains(id))
    circling.map(id => circling.filter(m => reach(id)(m) && reach(m)(id))).distinct

  /** A callee fixing a word left open above, whose Definition the caller's statement names. */
  private def leftOpenAndNamed(t: Theory, caller: NodeId)(callee: NodeId): Boolean =
    t.node(callee).map(_.statement).exists(s => s.relied == Reliance.LeftOpen &&
      s.definition.exists(mentions(t, caller).symbols.contains))
