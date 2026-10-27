package frflow.api.derive

import frflow.api.node.lean.ObligationState
import frflow.api.view.*
import frflow.core.consistency.{Consistency, Group, Standing, Vacuity}
import frflow.project.pipeline.Analysis
import frflow.proof.obligation.ObligationName

/** The theory's view, from the analysis and Lean's current results of `Whole.lean`. */
private[api] object Wholes:
  def of(a: Analysis): WholeView =
    WholeView(groups(a), Consistency.vacuity(a.decided.theory).map(v => v -> state(a, possible(v))),
      a.computed.examples.zipWithIndex.map { case ((e, onCode), i) =>
        ExampleView(e.name, if e.givens.nonEmpty then OnClaims.ScalaOnly
          else OnClaims.Lean(state(a, ObligationName.Example(i))), onCode)
      })

  /** `status` says it of each group Lean has not checked witnesses for. */
  def warnings(w: WholeView): List[Warning] =
    w.groups.filter(_.status != GroupStatus.Proven).map(g => Warning.ConsistencyNotProven(g.statements))

  private def groups(a: Analysis): List[GroupView] = Consistency.of(a.decided.theory).zipWithIndex.collect {
    case (g @ Group.Sharing(ids, _, _, ws), i) =>
      GroupView(ids, ws, standing(g.standing, state(a, ObligationName.Consistent(i))))
  }

  private def standing(s: Standing, lean: ObligationState): GroupStatus = (s, lean) match
    case (_, ObligationState.Proven) => GroupStatus.Proven
    case (Standing.Evidence(ts), _)  => GroupStatus.Evidence(ts)
    case _                           => GroupStatus.NotProven

  private def possible(v: Vacuity): ObligationName = v match
    case Vacuity.Inhabited(n, _)      => ObligationName.Inhabited(n)
    case Vacuity.Satisfiable(n, i, _) => ObligationName.Satisfiable(n, i)

  private def state(a: Analysis, n: ObligationName): ObligationState =
    a.wholeCheck.toList.flatMap(_.results).find(_.name == n).fold(ObligationState.Unchecked)(r => Leans.state(r.status))
