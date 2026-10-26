package frflow.api.view

import frflow.core.consistency.{Consistency, Group, Standing, Vacuity}
import frflow.project.pipeline.Analysis
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus

/** The theory's view, from the analysis and Lean's results of `Whole.lean`. */
object Wholes:
  def of(a: Analysis): WholeView =
    WholeView(groups(a), Consistency.vacuity(a.decided.theory).map(v => v -> status(a, possible(v))),
      a.computed.examples.zipWithIndex.map { case ((e, onCode), i) =>
        ExampleView(e.name, if e.givens.nonEmpty then OnClaims.ScalaOnly
          else OnClaims.Lean(status(a, ObligationName.Example(i))), onCode)
      })

  /** `status` says it of each group Lean has not checked witnesses for. */
  def warnings(w: WholeView): List[Warning] =
    w.groups.filter(_.status != GroupStatus.Proven).map(g => Warning.ConsistencyNotProven(g.statements))

  private def groups(a: Analysis): List[GroupView] = Consistency.of(a.decided.theory).zipWithIndex.collect {
    case (g @ Group.Sharing(ids, _, _, ws), i) => GroupView(ids, ws, standing(g.standing, status(a,
      ObligationName.Consistent(i))))
  }

  private def standing(s: Standing, lean: ObligationStatus): GroupStatus = (s, lean) match
    case (_, ObligationStatus.Proven)  => GroupStatus.Proven
    case (Standing.Evidence(ts), _)    => GroupStatus.Evidence(ts)
    case _                             => GroupStatus.NotProven

  private def possible(v: Vacuity): ObligationName = v match
    case Vacuity.Inhabited(n, _)      => ObligationName.Inhabited(n)
    case Vacuity.Satisfiable(n, i, _) => ObligationName.Satisfiable(n, i)

  private def status(a: Analysis, n: ObligationName): ObligationStatus =
    a.inputs.recorded.whole.find(_.name == n).fold(ObligationStatus.Unchecked)(_.status)
