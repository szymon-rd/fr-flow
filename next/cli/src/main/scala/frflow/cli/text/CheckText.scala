package frflow.cli.text

import frflow.api.node.NodeView
import frflow.api.node.lean.{CheckState, ObligationState}
import frflow.api.node.tests.TestOutcome
import frflow.api.view.View
import frflow.cli.say.{Findings, Tested, Unprovens}
import frflow.cli.term.{Marks, Style}
import frflow.core.name.NodeId
import frflow.decision.review.Cause

/** What `check` and `ci` print: each node checked, in a line and what keeps it from being proven; the theory as a
  * whole; then the summary and the warnings (`ci`: the nodes not proven, then `status`).
  */
object CheckText:
  def check(checked: List[NodeId], v: View, st: Style, layers: Contribution): List[String] =
    checked.flatMap(v.node).flatMap(node(_, st)) ++ WholeText.lines(v.whole, st, full = false) ++
      ("" :: SummaryText.lines(v, InboxText.waiting(v, layers.aside), st, layers.waiting)) ++
      TreeText.warnings(v, layers.warnings, st)

  def ci(v: View, st: Style, layers: Contribution): List[String] =
    val open = v.nodes.filterNot(proven).flatMap(node(_, st))
    open ++ (if open.isEmpty then Nil else List("")) ++ TreeText.status(v, st, layers)

  /** Nothing of it unproven, and its check not failing. */
  def proven(n: NodeView): Boolean = n.proof.unproven.isEmpty && !Marks.fails(n)

  /** `✓ id: what holds`, or what keeps it from it, then the details. */
  def node(n: NodeView, st: Style): List[String] =
    val glyph = if proven(n) then Marks.proven(st) else if Marks.fails(n) then Marks.failed(st) else Marks.open(st)
    s"$glyph ${st.bold(n.id.value)}: ${summary(n)}" :: details(n, st).map("  " + _)

  private def summary(n: NodeView): String =
    val tests = n.code.flatMap(_.tests)
    tests.map(_.outcome) match
      case Some(TestOutcome.Failed(f)) => Tested.failed(f, Cause.movedUnderCode(n.review.standing.causes))
      case _ if !proven(n)             => Findings.check(n.proof.state)
      case Some(TestOutcome.Passed)    =>
        (if n.proof.state == CheckState.Proven then "proven; its code" else "its code") +
          s" tested on ${tests.fold(0)(_.cases.tried)} cases"
      case _                           => if n.proof.state == CheckState.Proven then "proven" else "nothing to prove"

  private def details(n: NodeView, st: Style): List[String] =
    val fine = Set(ObligationState.Proven, ObligationState.Shown, ObligationState.Unchecked)
    val failing = n.proof.results.filterNot(r => fine(r.state))
    failing.flatMap(ProofText.obligation(_, st, full = false)) ++
      n.proof.findings.flatMap(Findings.lines(_, full = false)).map(st.red) ++
      n.proof.unproven.map(u => st.yellow(s"not proven: ${Unprovens.text(u)}")) ++
      n.code.flatMap(_.tests).toList.flatMap(t => t.unreached.map(Tested.target) ++ t.notes.map(Tested.note))
