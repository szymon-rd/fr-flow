package frflow.core.analysis

import cats.syntax.all.*
import frflow.core.expr.{Exprs, Mentions}
import frflow.core.graph.Walk
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{Reliance, Statement}
import frflow.core.Theory

/** A valid theory and a choice of definitions to its resolved relations. */
object Resolve:
  def apply(v: Valid, choice: Choice): Resolved =
    val t = v.theory
    val inForce = InForce.of(t, choice)
    val ids = t.nodes.map(_.node.id)
    val calls = ids.map(id => id -> calledBy(t, id)).toMap
    Resolved(t, inForce, ids.map(id => id -> uses(t, inForce, id)).toMap, calls,
      ids.map(id => id -> calls(id).filterNot(leftOpenAndNamed(t, id))).toMap)

  /** What a node's statement mentions, through the defines it calls. */
  def mentions(t: Theory, id: NodeId): Mentions =
    val own = t.node(id).toList.flatMap(_.statement.exprs).foldMap(Exprs.mentions)
    own |+| t.vocabulary.closure(own.defines).foldMap(d => Exprs.mentions(d.lambda.body))

  /** The definitions in force of the terms it mentions, and of those their definitions mention, nearest first. */
  private def uses(t: Theory, inForce: InForce, id: NodeId): List[NodeId] =
    def direct(n: NodeId) = fixedIn(mentions(t, n)).flatMap(inForce.fixedBy.get).filterNot(_ == n).distinct
    Walk.breadthFirst(direct(id), identity)(direct)

  private def fixedIn(m: Mentions): List[Fixed] = m.types.map(Fixed.Sort(_)) ++ m.symbols.map(Fixed.Term(_))

  /** The contracts on the operations its proven code calls, its own operation excepted. */
  private def calledBy(t: Theory, id: NodeId): List[NodeId] =
    val code = t.code.attached.get(id).flatMap(_.code.proven).toList
    val called = t.vocabulary.closure(code).flatMap(d => Exprs.mentions(d.lambda.body).symbols)
    val own = t.node(id).flatMap(_.statement.operation)
    def reliedOn(op: SymbolName) = called.contains(op) && !own.contains(op)
    t.nodes.map(_.node).filter(n => n.id != id && n.statement.operation.exists(reliedOn)).map(_.id)

  /** A callee fixing a word left open above, whose operation the caller's statement names. */
  private def leftOpenAndNamed(t: Theory, caller: NodeId)(callee: NodeId): Boolean =
    t.node(callee).map(_.statement).exists {
      case Statement.Contract(op, _, Reliance.LeftOpen)        => mentions(t, caller).symbols.contains(op)
      case Statement.FlowContract(op, _, _, Reliance.LeftOpen) => mentions(t, caller).symbols.contains(op)
      case _                                                   => false
    }
