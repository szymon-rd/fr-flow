package frflow.proof.whole

import cats.data.NonEmptyList
import frflow.core.analysis.{Callees, Constrained, Resolved}
import frflow.core.analysis.outside.Guards
import frflow.core.consistency.{Consistency, Defining, Group, Picked, Standing, Witness}
import frflow.core.expr.{Binder, OutsideFact, Value}
import frflow.core.graph.Walk
import frflow.core.name.{DefName, LeanNames, NodeId, SymbolName, VarId}
import frflow.core.spec.Range
import frflow.core.term.{Final, Stated, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.proof.obligation.{Constant, Discharge, Hyp, Obligation, ObligationName, Prop, Substitute, Supplied}

/** Consistency in Lean (owner §15, §18): the bottom statements and premises hold together (`consistent_<i>`, each
  * group with the witnesses derived for it), and each store's starting state meets what always holds of it
  * (`start_<node>`). A group nothing witnesses is still stated, and shows "consistency not proven" until the
  * developer proves it.
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
    case Group.Start(n, start) => start.flatMap(r.theory.node).flatMap(_.statement.outside).collect {
      case OutsideFact.Initially(m, rule) =>
        val state = r.theory.vocabulary.model(m).fold(Ty.Unit)(_.state)
        Obligation(ObligationName.Start(n), Prop.Starts(DefName(n.value), rule, state, within(r, n, state)),
          Discharge.Auto, s"Every state ${m.value} may start in meets ${n.value}.")
    }

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

  /** An `always[T]`'s rule at each `T` the state holds (the state itself, each element of a list, a record's
    * field), as the statement's guard places it on a variable of the state's type (2.6): over the state, level 0.
    * None for an `always(stored)`, whose rule is of the state.
    */
  private def within(r: Resolved, n: NodeId, state: Ty): Option[Final[Boolean]] =
    val about = r.theory.node(n).flatMap(_.statement.range).collect { case Range.Made(ty) => ty }
    Guards.byAlways(r.theory).collectFirst { case (`n`, g) => g }
      .filter(_ => about.exists(ty => Guards.applies(r.theory, ty, state))).map { g =>
        val s = Binder(VarId.level(0), "s", state)
        [T[_]] => (sym: Sym[T]) => g.of[T, Any](state, sym).fold(sym.bool(true))(_(sym.free[Any](s)))
      }

  private def names(ids: List[NodeId]): String = ids.map(_.value).mkString(", ")
  private def symbols(ss: List[SymbolName]): String = ss.map(_.value).mkString(", ")
