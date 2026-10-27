package frflow.cli.text

import frflow.api.node.lean.{ObligationState, ObligationView}
import frflow.api.node.{CodeView, NodeView}
import frflow.cli.say.{Findings, Tested}
import frflow.cli.term.Style
import frflow.core.checking.{Assumed, Tested as Piece}
import frflow.decision.review.Cause

/** What running things showed of a node: Lean's check (each obligation, why it ended where it did), and its code (how
  * each piece is shown to meet it, what testing found). `full`: every message whole.
  */
object ProofText:
  def sections(n: NodeView, st: Style, full: Boolean): List[(String, List[String])] =
    List("Proofs" -> proofs(n, st, full), "Code" -> n.code.toList.flatMap(code(_, n, st)))

  private def proofs(n: NodeView, st: Style, full: Boolean): List[String] =
    val p = n.proof
    if p.results.isEmpty && p.findings.isEmpty then Nil
    else s"check: ${Findings.check(p.state)}${if p.authored then " (with the developer's proof file)" else ""}" ::
      (p.results.flatMap(obligation(_, st, full)) ++ p.findings.flatMap(Findings.lines(_, full)).map(st.red))

  def obligation(o: ObligationView, st: Style, full: Boolean): List[String] =
    val fine = o.state == ObligationState.Proven || o.state == ObligationState.Shown
    val tone: String => String = if fine then st.green else if o.state == ObligationState.Unchecked then st.dim
      else st.red
    s"${o.theorem}: ${tone(Findings.obligation(o.state))}" :: (if fine && !full then Nil
      else Findings.messages(o.messages, full))

  private def code(c: CodeView, n: NodeView, st: Style): List[String] =
    val proven = c.shown.proven.map(_.value)
    val pieces = Option.when(proven.nonEmpty)(s"proven: ${proven.mkString(", ")}").toList ++
      c.shown.tested.map(tested) ++ c.shown.assumed.map(assumed)
    val tests = c.tests.fold(Option.when(c.shown.tested.nonEmpty)(st.yellow(Tested.NotYet)).toList)(t =>
      Tested.lines(t, Cause.movedUnderCode(n.review.standing.causes)))
    pieces ++ tests

  private def tested(t: Piece): String = t match
    case Piece.Plain  => "plain Scala, tested against it on generated cases: tested, not proven"
    case Piece.Own(i) => s"implementation ${i + 1}, the project's own, tested against the model"

  private def assumed(a: Assumed): String = a match
    case Assumed.Assumption => "an outside system's promise: assumed, its adapter tested against it"
    case Assumed.Outside(i) => s"implementation ${i + 1}, an outside system, checked against the model (the model " +
        "stays assumed)"
