package frflow.core.analysis.outside

import cats.syntax.all.*
import frflow.core.expr.{Expr, Exprs, Quantifier}
import frflow.core.name.{ModelName, NodeId, SymbolName}
import frflow.core.spec.{Node, Range}
import frflow.core.ty.Ty
import frflow.core.Theory
import frflow.core.analysis.{Callees, Constrained, Resolve, SaysWhat, Scope}

/** The one World kept local (owner §33): a statement reads only some stores, and takes only their rules as hypotheses
  * on the worlds it is about, so adding a store changes no statement that does not read it. A statement reads the
  * models whose state it mentions (through its defines), those of the operations the proven code standing in it calls,
  * and, for each Declaration it mentions, those the claims saying what that Declaration is read: a root over
  * Declarations reads the world as they are said to.
  */
object Reads:
  def models(t: Theory, id: NodeId): List[ModelName] =
    val meanings = Constrained.of(t, id).filter(Constrained.isDeclaration(t, _)).flatMap(saying(t, _))
    (direct(t, id) ++ meanings.filterNot(_ == id).flatMap(direct(t, _))).distinct

  /** The models a program reads and writes: those of the operations it calls. */
  def ofProgram(t: Theory, op: SymbolName): List[ModelName] =
    Callees.ofDefinition(t, op).toList.flatMap(_.calls.operations).flatMap(stored(t, _)).distinct

  /** Whether `id` takes the rule `rule` as a hypothesis: the rule's guard applies to a type the statement quantifies
    * over, or, of a world it quantifies over, to a store it reads.
    */
  def takes(t: Theory, id: NodeId, rule: NodeId): Boolean =
    guarded(t, id, rule) || fromOutside(t, id, rule)

  private def guarded(t: Theory, id: NodeId, rule: NodeId): Boolean =
    (t.node(id), t.node(rule).flatMap(_.statement.range)).tupled.exists { (n, r) =>
      val over = quantified(n)
      val worlds = over.contains(Ty.World) && Scope.models(t, r).map(_.name).exists(models(t, id).contains)
      worlds || (r match
        case Range.Made(ty) => over.exists(x => x != Ty.World && Guards.applies(t, ty, x))
        case _              => false)
    }

  /** An assumption of `always[U]` a statement's check rests on (`Premises`: its Lean or its obligations carry it). */
  private def fromOutside(t: Theory, id: NodeId, rule: NodeId): Boolean = t.node(rule).exists(a =>
    Outsides.aboutOutside(a) && Premises.of(t, id).exists(Outsides.saysOf(a, _)))

  /** The types of the variables a statement's formula quantifies over, or binds as a run's outcome and world. */
  def quantified(n: Node): List[Ty] = n.statement.said.toList.flatMap(f => Exprs.all(f.value).collect {
    case Expr.Quant(Quantifier.Forall | Quantifier.Exists, xs, _) => xs.map(_.ty)
  }.flatten)

  private def direct(t: Theory, id: NodeId): List[ModelName] =
    Resolve.mentions(t, id).models ++
      Callees.of(t, id).toList.flatMap(_.calls.operations).flatMap(stored(t, _))

  private def saying(t: Theory, d: SymbolName): List[NodeId] =
    t.nodes.map(_.node.id).filter(SaysWhat.declarations(t, _).contains(d))

  private def stored(t: Theory, op: SymbolName): List[ModelName] = t.vocabulary.modelOf(op).map(_.name).toList
