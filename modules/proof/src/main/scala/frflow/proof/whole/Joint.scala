package frflow.proof.whole

import cats.data.NonEmptyList
import frflow.core.analysis.resolution.{Callees, Constrained, Resolved}
import frflow.core.consistency.{Consistency, Defining, Group, Picked, Standing, Witness}
import frflow.core.expr.Value
import frflow.core.graph.Walk
import frflow.core.name.{LeanNames, NodeId, SymbolName}
import frflow.core.term.language.Stated
import frflow.core.vocab.SymbolType
import frflow.proof.obligation.{Constant, Discharge, Hyp, Obligation, ObligationName, Prop, Substitute, Supplied}

/** Consistency as the prover is asked it (owner §15, §18): the bottom statements and premises hold together
  * (`consistent_<i>`, each group with the witnesses derived for it). A group nothing witnesses is still stated, and
  * shows "consistency not proven" until the developer proves it.
  */
object Joint:
  def of(r: Resolved): List[Obligation] =
    Consistency.of(r.theory).zipWithIndex.flatMap((g, i) => group(r, g, i))

  private def group(r: Resolved, g: Group, i: Int): Option[Obligation] = g match
    case g @ Group.Sharing(ids, open, provided, _, premises) =>
      NonEmptyList.fromList(ids).map { ns =>
        val some = Prop.ForSome(open, Prop.Both(ns.map(Prop.ClaimOf(_, standing(r, ids)))))
        val says = premises.map(p => Hyp(LeanNames.hypothesis(p), Prop.ClaimOf(p, standing(r, List(p)))))
        val goal = Prop.ForEvery(provided, if says.isEmpty then some else Prop.Implies(says, some))
        Obligation(ObligationName.Consistent(i), goal, witnessed(r, g),
          s"${names(ids)} hold together: some meaning of ${symbols(open)} makes each true" +
            (if provided.isEmpty then "." else s", for every ${symbols(provided)} provided") +
            (if premises.isEmpty then (if provided.isEmpty then "" else ".")
            else s" as ${names(premises)} ${if premises.size == 1 then "says" else "say"}."))
      }
    case g @ Group.Premises(_, _, _) => premised(r, g, i)

  /** The premises over the same provided values: some value of each meets them all. */
  private def premised(r: Resolved, g: Group.Premises, i: Int): Option[Obligation] =
    NonEmptyList.fromList(g.statements).map { ns =>
      Obligation(ObligationName.Consistent(i), Prop.ForSome(g.provided, Prop.Both(ns.map(Prop.ClaimOf(_,
        standing(r, g.statements))))), if g.standing == Standing.Witnessed then
          Discharge.Witnessed(g.witnesses.flatMap(supplied(r, _))) else Discharge.Unwitnessed,
        s"${names(g.statements)} can hold together: some ${symbols(g.provided)} provided meets each.")
    }

  /** What stands for each Definition the group's statements mention that is not open: its proven code or value. */
  private def standing(r: Resolved, ids: List[NodeId]): Map[SymbolName, Substitute] =
    Stands.of(r, ids.flatMap(Constrained.of(r.theory, _)))

  private def witnessed(r: Resolved, g: Group.Sharing): Discharge = g.standing match
    case Standing.Witnessed => Discharge.Witnessed(ordered(r, g))
    case _                  => Discharge.Unwitnessed

  /** The witnesses in solving order, each proven code the statements mention or that code reaches given as its
    * define just before the first witness that may mention it: once every value it leaves open is solved, and after
    * the code standing for each Definition it calls.
    */
  private def ordered(r: Resolved, g: Group.Sharing): List[Supplied] =
    val stands = standing(r, g.statements).collect { case (s, Substitute.Code(d)) => (s, d) }
    val code = Walk.postorder(stands.keys.toList.sortBy(_.value), identity)(s =>
      Callees.ofDefinition(r.theory, s).toList.flatMap(_.calls.symbols).filter(stands.contains))
      .flatMap(s => stands.get(s).map(s -> _))
    g.witnesses.foldLeft((List.empty[Supplied], List.empty[SymbolName])) { case ((out, solved), w) =>
      val ready = code.filter((s, d) =>
        !out.contains(Supplied.Code(s, d)) && Consistency.reach(r.theory, s).forall(solved.contains))
      (out ++ ready.map(Supplied.Code(_, _)) ++ supplied(r, w), solved :+ w.meaningOf)
    }._1

  private def supplied(r: Resolved, w: Witness): Option[Supplied] = w match
    case Witness.Equation(s, from, picked) => term(r, s, from, picked)
    case Witness.Bound(s, from, picked)    => term(r, s, from, picked)
    case Witness.Empty(s)                  => r.theory.vocabulary.symbol(s).map(_.ty).collect {
        case SymbolType.Typed(ty) => Supplied.Value(Constant(Value.Many(Nil), ty))
      }
    case Witness.Tested(_) | Witness.Missing(_) => None

  private def term(r: Resolved, s: SymbolName, from: NodeId, picked: Picked): Option[Supplied] =
    r.theory.node(from).flatMap(_.statement.said).map(f => Supplied.Term(Stated(Defining.of(f.term, picked)), s))

  private def names(ids: List[NodeId]): String = ids.map(_.value).mkString(", ")
  private def symbols(ss: List[SymbolName]): String = ss.map(_.value).mkString(", ")
