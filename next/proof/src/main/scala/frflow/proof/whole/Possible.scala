package frflow.proof.whole

import frflow.core.analysis.{Constrained, Resolved}
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
        val meets = Consistency.meets(r.theory, n, ty)
        Some(Obligation(ObligationName.Inhabited(n), Prop.Inhabited(meets, ty), by,
          if !meets.contains(DefName(n.value)) then s"Some state meets what ${n.value} says the store starts in."
          else if meets.size > 1 then s"Some value meets ${meets.map(_.value).mkString(", ")} together."
          else s"Some value meets ${n.value}."))
      case Vacuity.Satisfiable(n, i, _) => Consistency.condition(r.theory, n, i).map(c =>
        Obligation(ObligationName.Satisfiable(n, i), Prop.ForSome(Consistency.opens(r.theory, c),
          Prop.Formula(c, Stands.of(r, Constrained.of(r.theory, n)))), by,
          s"Condition ${i + 1} of ${n.value} can hold."))
