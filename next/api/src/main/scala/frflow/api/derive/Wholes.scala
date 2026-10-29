package frflow.api.derive

import frflow.api.node.lean.{ObligationState, ObligationView}
import frflow.api.view.Warning
import frflow.api.view.whole.*
import frflow.core.consistency.{Consistency, Group, Standing, Vacuity}
import frflow.proof.lean.lower.LowerObligation
import frflow.project.pipeline.Analysis
import frflow.proof.obligation.ObligationName

/** The theory's view, from the analysis and Lean's current results of `Whole.lean`: each obligation with its outcome
  * and Lean's messages, unchecked while there is none.
  */
private[api] object Wholes:
  def of(a: Analysis): WholeView =
    val groups = Consistency.of(a.decided.theory).zipWithIndex
    WholeView(groups.collect { case (g @ Group.Sharing(ids, _, _, ws, _), i) =>
        val c = check(a, ObligationName.Consistent(i))
        GroupView(ids, ws, standing(g.standing, c.state), c)
      },
      groups.collect { case (Group.Start(n, start), _) => StartView(n, start, check(a, ObligationName.Start(n))) },
      Consistency.vacuity(a.decided.theory).map(v => v -> check(a, possible(v))),
      a.computed.examples.zipWithIndex.map { case ((e, onCode), i) =>
        ExampleView(e.name, if e.givens.nonEmpty then OnClaims.ScalaOnly
          else OnClaims.Lean(check(a, ObligationName.Example(i))), onCode)
      })

  /** `status` says it of each group Lean has not checked witnesses for, and each start not proven. */
  def warnings(w: WholeView): List[Warning] =
    w.groups.filter(_.status != GroupStatus.Proven).map(g => Warning.ConsistencyNotProven(g.statements)) ++
      w.starts.filter(_.check.state != ObligationState.Proven).map(s => Warning.StartNotProven(s.statement))

  private def standing(s: Standing, lean: ObligationState): GroupStatus = (s, lean) match
    case (_, ObligationState.Proven) => GroupStatus.Proven
    case (Standing.Evidence(ts), _)  => GroupStatus.Evidence(ts)
    case _                           => GroupStatus.NotProven

  private def possible(v: Vacuity): ObligationName = v match
    case Vacuity.Inhabited(n, _)      => ObligationName.Inhabited(n)
    case Vacuity.Satisfiable(n, i, _) => ObligationName.Satisfiable(n, i)

  private def check(a: Analysis, n: ObligationName): ObligationView =
    a.wholeCheck.toList.flatMap(_.results).find(_.name == n).map(Leans.of)
      .getOrElse(ObligationView(LowerObligation.name(n).text, ObligationState.Unchecked, Nil))
