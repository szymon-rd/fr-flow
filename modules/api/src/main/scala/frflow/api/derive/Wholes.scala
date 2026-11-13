package frflow.api.derive

import frflow.api.node.proving.{ObligationState, ObligationView}
import frflow.api.view.Warning
import frflow.api.view.whole.*
import frflow.core.consistency.{Consistency, Group, Standing, Vacuity}
import frflow.proof.prover.lower.LowerObligation
import frflow.project.pipeline.Analysis
import frflow.proof.obligation.ObligationName

/** The theory's view, from the analysis and Rocq's current results of `Whole.v`: each obligation with its outcome
  * and Rocq's messages, unchecked while there is none.
  */
private[api] object Wholes:
  def of(a: Analysis): WholeView =
    val groups = Consistency.of(a.decided.theory).zipWithIndex
    WholeView(groups.map(group(a, _, _)),
      Consistency.vacuity(a.decided.theory).map(v => v -> check(a, possible(v))),
      a.computed.examples.map { (e, onCode) =>
        ExampleView(e.name, if e.givens.nonEmpty then OnClaims.ScalaOnly
          else OnClaims.Rocq(check(a, ObligationName.Example(e.of, e.at)),
            check(a, ObligationName.ExampleOpposite(e.of, e.at))), onCode)
      })

  /** A group of statements or of premises, with the prover's check of it. */
  private def group(a: Analysis, g: Group, i: Int): GroupView =
    val c = check(a, ObligationName.Consistent(i))
    val (ids, ws) = g match
      case Group.Sharing(ids, _, _, ws, _) => ids -> ws
      case Group.Premises(ids, _, ws)      => ids -> ws
    GroupView(ids, ws, standing(g.standing, c.state), c)

  /** `status` says it of each group the prover has not checked witnesses for. */
  def warnings(w: WholeView): List[Warning] =
    w.groups.filter(_.status != GroupStatus.Proven).map(g => Warning.ConsistencyNotProven(g.statements))

  private def standing(s: Standing, rocq: ObligationState): GroupStatus = (s, rocq) match
    case (_, ObligationState.Proven) => GroupStatus.Proven
    case (Standing.Evidence(ts), _)  => GroupStatus.Evidence(ts)
    case _                           => GroupStatus.NotProven

  private def possible(v: Vacuity): ObligationName = v match
    case Vacuity.Inhabited(n, _)      => ObligationName.Inhabited(n)
    case Vacuity.Satisfiable(n, i, _) => ObligationName.Satisfiable(n, i)

  private def check(a: Analysis, n: ObligationName): ObligationView =
    a.wholeCheck.toList.flatMap(_.results).find(_.name == n).map(ProofViews.of)
      .getOrElse(ObligationView(LowerObligation.name(n).text, ObligationState.Unchecked, Nil))
