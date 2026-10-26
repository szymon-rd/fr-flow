package frflow.proof.whole

import cats.data.NonEmptyList
import frflow.core.analysis.{Callees, Constrained, Resolved}
import frflow.core.code.Code
import frflow.core.consistency.{Consistency, Defining, Group, Picked, Standing, Witness}
import frflow.core.expr.OutsideFact
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.term.Stated
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.proof.obligation.{Constant, Discharge, Obligation, ObligationName, Prop, Substitute, Supplied}

/** Consistency in Lean (owner §15, §18): the bottom statements and premises hold together (`consistent_<i>`, each
  * group with the witnesses derived for it), and each store's starting state meets what always holds of it
  * (`start_<node>`). A group nothing witnesses is still stated, and shows "consistency not proven" until the
  * developer proves it.
  */
object Joint:
  def of(r: Resolved): List[Obligation] =
    Consistency.of(r.theory).zipWithIndex.flatMap((g, i) => group(r, g, i))

  private def group(r: Resolved, g: Group, i: Int): Option[Obligation] = g match
    case g @ Group.Sharing(ids, open, provided, ws) =>
      NonEmptyList.fromList(ids).map { ns =>
        val goal = Prop.ForEvery(provided, Prop.ForSome(open, Prop.Both(ns.map(Prop.ClaimOf(_, standing(r, ids))))))
        Obligation(ObligationName.Consistent(i), goal, witnessed(r, g.standing, ws),
          s"${names(ids)} hold together: some meaning of ${symbols(open)} makes each true" +
            (if provided.isEmpty then "." else s", for every ${symbols(provided)} provided."))
      }
    case Group.Start(n, start) => start.flatMap(r.theory.node).flatMap(_.statement.outside).collect {
      case OutsideFact.Initially(m, rule) =>
        val state = r.theory.vocabulary.model(m).fold(Ty.Unit)(_.state)
        Obligation(ObligationName.Start(n), Prop.Starts(DefName(n.value), each(r, n, state), rule, state),
          Discharge.Auto, s"Every state ${m.value} may start in meets ${n.value}.")
    }

  /** What stands for each Definition the group's statements mention that is not open: its proven code or value. */
  private def standing(r: Resolved, ids: List[NodeId]): Map[SymbolName, Substitute] =
    ids.flatMap(Constrained.of(r.theory, _)).distinct.flatMap(s => r.theory.code.attached.get(s).map(_.code).collect {
      case Code.Valued(v)                       => s -> Substitute.Fixed(Constant(v, typeOf(r, s)))
      case Code.Proven(_) | Code.ProvenFlow(_) =>
        s -> Callees.ofDefinition(r.theory, s).flatMap(_.standsFor.get(s)).fold(Substitute.Nothing)(Substitute.Code(_))
    }).toMap

  private def typeOf(r: Resolved, s: SymbolName): Ty = r.theory.vocabulary.symbol(s).map(_.ty).collect {
    case SymbolType.Typed(t) => t
  }.getOrElse(Ty.Unit)

  private def witnessed(r: Resolved, standing: Standing, ws: List[Witness]): Discharge = standing match
    case Standing.Witnessed => Discharge.Witnessed(ws.flatMap(supplied(r, _)))
    case _                  => Discharge.Unwitnessed

  private def supplied(r: Resolved, w: Witness): Option[Supplied] = w match
    case Witness.Equation(s, from, picked) => term(r, s, from, picked)
    case Witness.Bound(s, from, picked)    => term(r, s, from, picked)
    case Witness.Tested(_) | Witness.Missing(_) => None

  private def term(r: Resolved, s: SymbolName, from: NodeId, picked: Picked): Option[Supplied] =
    r.theory.node(from).flatMap(_.statement.said).map(f => Supplied.Term(Stated(Defining.of(f.term, picked)), s))

  /** Whether the rule is of each element of the state (an `always[T]` of a store holding a list of `T`). */
  private def each(r: Resolved, n: NodeId, state: Ty): Boolean =
    r.theory.vocabulary.define(DefName(n.value)).exists(_.lambda.params.headOption.exists(_.ty != state))

  private def names(ids: List[NodeId]): String = ids.map(_.value).mkString(", ")
  private def symbols(ss: List[SymbolName]): String = ss.map(_.value).mkString(", ")
