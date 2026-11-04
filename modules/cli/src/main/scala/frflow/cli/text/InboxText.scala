package frflow.cli.text

import frflow.api.node.NodeView
import frflow.api.view.{View, Views}
import frflow.cli.say.Unprovens
import frflow.cli.term.Style
import frflow.core.name.NodeId
import frflow.decision.review.ReviewState

/** What waits for the developer (`inbox`): the mechanical batch, each node to decide in order with why, the decided
  * nodes gone from the model, what layers on top add, then the summary.
  */
object InboxText:
  def lines(v: View, st: Style, layers: Contribution): List[String] =
    val (batch, rest) = queue(v, layers.aside).partition(mechanical)
    val body = Lines.section("Mechanical: Lean proves them again, and nothing in them is a choice (confirm takes them)",
        batch.map(Lines.node(_, st, 2)), st) ++
      Lines.section("To decide, in order (review, or accept / reject NODE)", rest.flatMap(waits(_, st)), st) ++
      Lines.section("Gone from the model (gone NODE agrees it is gone)", v.gone.map(_.value), st) ++
      layers.inbox.flatMap((title, ls) => Lines.section(title, ls, st))
    val head = if body.isEmpty then List("Nothing waits for the developer.") else body.drop(1)
    head ++ ("" :: SummaryText.lines(v, waiting(v, layers.aside), st, layers.waiting))

  /** The nodes waiting, in the order to decide them. */
  def queue(v: View, aside: Set[NodeId]): List[NodeView] = Views.inbox(v, aside).flatMap(v.node)

  /** How many nodes wait for the developer, the gone ones among them. */
  def waiting(v: View, aside: Set[NodeId]): Int = Views.inbox(v, aside).size + v.gone.size

  /** Under review, and `confirm` takes it in its batch. */
  def mechanical(n: NodeView): Boolean =
    n.review.standing.state == ReviewState.Review && n.review.notMechanical.isEmpty

  /** Its line, and why it waits: what moved, or what it waits for. */
  def waits(n: NodeView, st: Style): List[String] =
    val why = n.review.waitsFor.map(w => s"decide $w first: what rests on it is decided after it")
      .orElse(Option.when(n.review.standing.state == ReviewState.Review)(
        s"to review: ${n.review.standing.causes.map(Unprovens.cause).mkString("; ")}"))
    Lines.node(n, st, 2) :: why.toList.map(w => st.fit(st.dim(s"  $w"), 2))
