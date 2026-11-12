package frflow.proof.whole

import frflow.core.analysis.resolution.{Callees, Constrained, Resolved}
import frflow.core.consistency.{Consistency, Vacuity}
import frflow.core.name.DefName
import frflow.proof.obligation.{Constant, Discharge, Obligation, ObligationName, Prop, Supplied}

/** Vacuity in Lean (owner §18): each `always[T]` admits a value (`inhabited_<node>`) and each claim's condition can
  * hold (`satisfiable_<i>_<node>`), with the values the search found (`found`); one with none found is still stated,
  * and shows "not shown".
  */
object Possible:
  def of(r: Resolved, found: Map[Vacuity, List[Constant]]): List[Obligation] =
    Consistency.vacuity(r.theory).flatMap(possible(r, found))

  private def possible(r: Resolved, found: Map[Vacuity, List[Constant]])(v: Vacuity): Option[Obligation] =
    val by = found.get(v).fold(Discharge.Unwitnessed)(cs => Discharge.Witnessed(cs.map(Supplied.Value(_))))
    v match
      case Vacuity.Inhabited(n, ty)     =>
        val meets = Consistency.meets(r.theory, ty)
        Some(Obligation(ObligationName.Inhabited(n), Prop.Inhabited(meets, ty), by,
          if meets.size > 1 then s"Some value meets ${meets.map(_.value).mkString(", ")} together."
          else s"Some value meets ${n.value}."))
      case Vacuity.Satisfiable(n, i, _) => Consistency.condition(r.theory, n, i).map { c =>
        val opens = Consistency.opens(r.theory, c)
        val why = unwitnessed(r, n, opens)
        Obligation(ObligationName.Satisfiable(n, i), Prop.ForSome(opens,
          Prop.Formula(c, Stands.of(r, Constrained.of(r.theory, n)))), if why.nonEmpty then Discharge.Unwitnessed
          else by, s"Condition ${i + 1} of ${n.value} can hold." + why.fold("")(" " + _))
      }

  /** Why no witness shows a condition: it is about Declarations (a witness would choose what they mean, whatever the
    * claims say), or the code standing in it calls code not proven, which Lean takes as open and no witness gives.
    */
  private def unwitnessed(r: Resolved, n: frflow.core.name.NodeId, opens: List[frflow.core.name.SymbolName])
      : Option[String] =
    val mentioned = Constrained.of(r.theory, n)
    val reached = Callees.reaching(r.theory, mentioned).filter(s => !opens.contains(s) && !mentioned.contains(s) &&
      r.theory.code.attached.get(s).forall(_.code.proven.isEmpty))
    if opens.exists(Constrained.isDeclaration(r.theory, _)) then
      Some("It is about Declarations: a witness would choose what they mean, whatever the claims say, so it is not " +
        "shown by one.")
    else Option.when(reached.nonEmpty)(s"The code standing in it calls ${reached.map(_.value).mkString(", ")}, " +
      "which no witness gives, so it is not shown by one.")
