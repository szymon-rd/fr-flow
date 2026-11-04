package frflow.cli.term

import frflow.api.node.NodeView
import frflow.api.node.lean.CheckState
import frflow.api.node.tests.TestOutcome
import frflow.decision.review.ReviewState

/** The mark before a node, and the colors of its review state. */
object Marks:
  /** ✓ proven (nothing of it unproven), ○ not proven, ✗ fails (its check, or a generated case of its code), … waiting,
    * ? not checked yet, · nothing to prove; ! a node the developer is to decide (new, or back for review), unless it
    * fails: its proof is not what to look at then.
    */
  def glyph(n: NodeView, st: Style): String =
    val decide = n.review.standing.state == ReviewState.Proposed || n.review.standing.state == ReviewState.Review
    if fails(n) then failed(st)
    else if decide then st.yellow("!")
    else n.proof.state match
      case CheckState.Proven                               => if n.proof.unproven.isEmpty then proven(st) else open(st)
      case CheckState.Open                                 => open(st)
      case CheckState.Waiting | CheckState.Timeout         => st.yellow(st.pick("…", "."))
      case CheckState.Unchecked if nothingToProve(n)       => st.dim(st.dot)
      case _                                               => st.dim("?")

  def fails(n: NodeView): Boolean =
    n.proof.state == CheckState.Failed || n.proof.state == CheckState.ModelError ||
      n.code.flatMap(_.tests).exists(_.outcome match
        case TestOutcome.Failed(_) => true
        case _                     => false)

  private def nothingToProve(n: NodeView): Boolean = n.proof.results.isEmpty && n.proof.unproven.isEmpty

  def proven(st: Style): String = st.green(st.pick("✓", "+"))
  def open(st: Style): String = st.yellow(st.pick("○", "o"))
  def failed(st: Style): String = st.red(st.pick("✗", "x"))

  def state(s: ReviewState, text: String, st: Style): String = s match
    case ReviewState.Accepted => st.green(text)
    case ReviewState.Proposed => st.cyan(text)
    case ReviewState.Review   => st.yellow(text)
    case ReviewState.Rejected => st.red(text)

  /** What the marks before the nodes say, on one line. */
  def legend(st: Style): String =
    st.dim("marks: ") + List(proven(st) -> "proven or tested", failed(st) -> "fails", open(st) -> "not proven",
      "?" -> "not checked yet", st.dim(st.dot) -> "nothing to prove", "!" -> "to decide")
      .map((m, w) => s"$m ${st.dim(w)}").mkString("  ")
